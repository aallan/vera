"""Vera module resolver — map import paths to source files.

C7a: Resolve import declarations to files on disk, parse them into
ASTs, cache results, and detect circular imports. Does NOT merge
types across modules (C7b) or enforce visibility (C7c).
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field, replace
from pathlib import Path

from vera import ast
from vera.errors import (
    Diagnostic,
    ParseError,
    SourceLocation,
    TransformError,
)
from vera.parser import parse_file
from vera.transform import transform


@dataclass(frozen=True)
class ResolvedModule:
    """A resolved and parsed module.

    ``direct`` marks whether the top-level program imports this module
    directly (``import mid;``) versus only reaches it transitively through
    another module's imports (``main`` imports ``mid`` which imports
    ``base`` → ``base`` is transitive-only).  All reachable modules are
    returned so the importer's flat WASM module can compile every body it
    calls into (#890), but per spec §8.6.4 a transitive module's public
    declarations are *not* visible to the original importer — only the
    direct imports are injected into the importer's callable namespace.
    Defaults to ``True`` so hand-built ``ResolvedModule`` fixtures (which
    model a direct import) keep their existing meaning.
    """

    path: tuple[str, ...]  # e.g., ("vera", "math")
    file_path: Path  # absolute path to the .vera file
    program: ast.Program  # parsed + transformed AST
    source: str  # raw source text
    direct: bool = True  # imported by the top-level program (vs transitive)


@dataclass
class ModuleResolver:
    """Resolves import paths to source files and parses them.

    Resolution algorithm (C7a, simple):
    1. Convert module path to directory separators + ".vera" suffix
       e.g., ``vera.math`` → ``vera/math.vera``
    2. Resolve relative to the importing file's parent directory
    3. If the importing file's parent differs from the root, also
       try relative to the root directory

    Circular imports are detected and reported as diagnostics.
    Parsed modules are cached so each file is parsed at most once.
    """

    _root: Path
    _cache: dict[tuple[str, ...], ResolvedModule] = field(
        default_factory=dict,
    )
    _in_progress: set[tuple[str, ...]] = field(default_factory=set)
    _errors: list[Diagnostic] = field(default_factory=list)

    @property
    def errors(self) -> list[Diagnostic]:
        """Accumulated resolution diagnostics."""
        return list(self._errors)

    # -----------------------------------------------------------------
    # Public API
    # -----------------------------------------------------------------

    def resolve_imports(
        self,
        program: ast.Program,
        file: Path,
    ) -> list[ResolvedModule]:
        """Resolve all imports in a program, transitively (#890).

        Returns every module reachable through the import graph, not just
        the top-level program's direct imports.  A module named in
        ``program.imports`` is tagged ``direct=True``; a module reached only
        through another module's imports is ``direct=False``.  Both are
        returned so the importer's flat WASM module can compile every body it
        transitively calls into — but consumers inject only the DIRECT
        imports into the importer's callable namespace (spec §8.6.4:
        transitive declarations are not visible to the original importer).

        Each file is resolved (parsed) at most once via the cache.  Errors
        are accumulated in ``self.errors``.
        """
        # Direct imports first — resolving each also recursively resolves and
        # caches its own imports (``_resolve_single``), so after this loop the
        # cache holds the full reachable closure.
        direct_paths: set[tuple[str, ...]] = set()
        for imp in program.imports:
            mod = self._resolve_single(imp, file)
            if mod is not None:
                direct_paths.add(mod.path)

        # Assemble the closure from the cache.  Emit direct imports (in source
        # order) first, then the transitive-only modules, deduplicated by path
        # so a diamond (two importers of one base) yields the base once.
        resolved: list[ResolvedModule] = []
        seen: set[tuple[str, ...]] = set()

        def _emit(mod: ResolvedModule, *, direct: bool) -> None:
            if mod.path in seen:
                return
            seen.add(mod.path)
            # ``mod`` is cached with ``direct=True`` (the dataclass default);
            # re-tag it so a transitively-reached module is not treated as a
            # direct import by the importer's namespace injection.
            resolved.append(mod if direct else replace(mod, direct=False))

        for imp in program.imports:
            mod = self._cache.get(imp.path)
            if mod is not None:
                _emit(mod, direct=True)
        for path, mod in self._cache.items():
            _emit(mod, direct=path in direct_paths)

        return resolved

    # -----------------------------------------------------------------
    # Internal
    # -----------------------------------------------------------------

    def _resolve_single(
        self,
        imp: ast.ImportDecl,
        importing_file: Path,
    ) -> ResolvedModule | None:
        """Resolve a single import declaration.

        Returns the ResolvedModule or None on failure (error recorded).
        """
        mod_path = imp.path

        # Check cache first
        if mod_path in self._cache:
            return self._cache[mod_path]

        # Circular import detection
        if mod_path in self._in_progress:
            self._errors.append(
                Diagnostic(
                    description=(
                        f"Circular import detected: "
                        f"'{'.'.join(mod_path)}' is already being "
                        f"resolved."
                    ),
                    location=self._location_from_node(imp, importing_file),
                    source_line=self._source_line(importing_file, imp),
                    rationale=(
                        "Circular imports are not allowed. The module "
                        "dependency graph must be acyclic."
                    ),
                    fix=(
                        "Break the cycle: remove one of the imports, or "
                        "extract the shared declarations into a third "
                        "module that both modules import."
                    ),
                    spec_ref=(
                        'Chapter 8, Section 8.6.3 '
                        '"Circular Import Detection"'
                    ),
                    severity="error",
                    error_code="E011",
                ),
            )
            return None

        # Resolve path to file on disk
        file_path = self._resolve_path(mod_path, importing_file)
        if file_path is None:
            self._errors.append(
                Diagnostic(
                    description=(
                        f"Cannot resolve import "
                        f"'{'.'.join(mod_path)}': no file found."
                    ),
                    location=self._location_from_node(imp, importing_file),
                    source_line=self._source_line(importing_file, imp),
                    rationale=(
                        f"Looked for "
                        f"'{'/'.join(mod_path)}.vera' relative to "
                        f"the importing file and project root."
                    ),
                    fix=(
                        f"Create the file "
                        f"'{'/'.join(mod_path)}.vera' or check the "
                        f"import path."
                    ),
                    spec_ref=(
                        'Chapter 8, Section 8.6.1 "Path Mapping"'
                    ),
                    severity="error",
                    error_code="E012",
                ),
            )
            return None

        # Mark as in-progress (circular detection)
        self._in_progress.add(mod_path)

        try:
            # Parse and transform
            source = file_path.read_text(encoding="utf-8")
            tree = parse_file(str(file_path))
            program = transform(tree)

            mod = ResolvedModule(
                path=mod_path,
                file_path=file_path,
                program=program,
                source=source,
            )

            # Recursively resolve imports of the imported module
            # BEFORE adding to cache — so circular imports are caught
            # by the _in_progress check rather than short-circuited
            # by the cache.
            for sub_imp in program.imports:
                self._resolve_single(sub_imp, file_path)

            self._cache[mod_path] = mod
            return mod
        except (
            ParseError, TransformError, OSError, UnicodeDecodeError,
        ) as exc:
            # Only genuine resolution failures of the imported file become
            # E013: ParseError/TransformError from parse_file/transform, and
            # OSError/UnicodeDecodeError from read_text.  Any other exception
            # is an internal compiler bug and must propagate, not be relabeled
            # as the user's module failing to parse.
            self._errors.append(
                Diagnostic(
                    description=(
                        f"Error parsing imported module "
                        f"'{'.'.join(mod_path)}': {exc}"
                    ),
                    location=self._location_from_node(imp, importing_file),
                    source_line=self._source_line(importing_file, imp),
                    rationale=(
                        "An imported module must itself parse and "
                        "transform successfully before its declarations "
                        "can be used by the importing program."
                    ),
                    fix=(
                        f"Run `vera check {'/'.join(mod_path)}.vera` "
                        f"directly to see the detailed syntax diagnostic, "
                        f"then correct the imported module."
                    ),
                    spec_ref=(
                        'Chapter 8, Section 8.6.5 "Resolution Errors"'
                    ),
                    severity="error",
                    error_code="E013",
                ),
            )
            return None
        finally:
            self._in_progress.discard(mod_path)

    def _resolve_path(
        self,
        mod_path: tuple[str, ...],
        importing_file: Path,
    ) -> Path | None:
        """Map a module path to a file on disk.

        Tries:
        1. Relative to the importing file's parent directory
        2. Relative to the project root (if different)
        """
        relative = Path(*mod_path).with_suffix(".vera")

        # Try relative to importing file's directory
        candidate = importing_file.parent / relative
        if candidate.is_file():
            return candidate.resolve()

        # Try relative to the project root
        root_candidate = self._root / relative
        if root_candidate.is_file():
            return root_candidate.resolve()

        return None

    @staticmethod
    def _location_from_node(
        node: ast.Node, importing_file: Path | None = None,
    ) -> SourceLocation:
        """Extract a SourceLocation from an AST node's span.

        ``importing_file`` names the file that contains ``node`` (the
        importing program); threading it through populates
        ``location.file`` so resolver diagnostics match the file-qualified
        location every checker diagnostic carries.
        """
        file = str(importing_file) if importing_file is not None else None
        if node.span:
            return SourceLocation(
                file=file,
                line=node.span.line,
                column=node.span.column,
            )
        return SourceLocation(file=file)

    @staticmethod
    def _source_line(importing_file: Path, node: ast.Node) -> str:
        """Read the offending import line from the importing file.

        Best-effort: a missing or unreadable file yields ``""`` rather
        than raising, since the source line is contextual, not essential.
        Mirrors the checker's ``_source_line`` so ``vera check --json``
        carries the offending line for resolver errors too.
        """
        if not node.span:
            return ""
        try:
            lines = importing_file.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError):
            return ""
        idx = node.span.line - 1
        return lines[idx] if 0 <= idx < len(lines) else ""


def merged_import_filters(
    decls: Iterable[ast.ImportDecl],
) -> dict[tuple[str, ...], set[str] | None]:
    """One filter per imported PATH, unioned across repeated imports (#1433).

    The ONE derivation of what a namespace's import list admits from each
    module: ``None`` for a whole-module import, else the set of names.  The
    checker, the verifier and code generation all read it, so they cannot
    disagree about a program that imports one module twice — each used to
    key its own table on the path, the last statement winning, and a
    qualified call to a name only the FIRST list admitted was refused with
    E231 while its bare call ran.

    A namespace may name a declaration that ANY of its import lists admits,
    so two statements naming one module contribute the union of their
    lists and a wildcard dominates every list beside it.  Keying a dict
    comprehension on the path instead made the LAST statement win and
    discarded the others (PR review): with
    ``import liba(aone); import liba(helper);`` the surviving filter admits
    neither the type nor the signature that carries it, so #1317's flow
    condition would stop seeing a crossing the entry can actually make and
    the rename would qualify apart two declarations a value passes between.

    Dedupe is idempotent by construction: repeating one statement adds
    nothing (spec §8.5.5).
    """
    out: dict[tuple[str, ...], set[str] | None] = {}
    for imp in decls:
        names = set(imp.names) if imp.names is not None else None
        if imp.path not in out:
            out[imp.path] = names
            continue
        existing = out[imp.path]
        if existing is None or names is None:
            out[imp.path] = None  # a wildcard admits everything
        else:
            out[imp.path] = existing | names
    return out


def own_module_path(
    program: ast.Program,
    resolved_as: tuple[str, ...] | None,
    resolved: Iterable[ResolvedModule],
) -> tuple[str, ...] | None:
    """The path that names *program*'s own file in a qualified call (#1558).

    A module's identity is the path its ``module`` declaration gives (§8.2),
    and a module-qualified call names a module by its path (§8.5.3), so
    inside the file that path names the file itself: ``ma::two(3)`` in
    ``module ma;`` calls its own ``two``.  The ONE derivation of which path
    that is, read by the checker (which resolves the call) and the verifier
    (which reads the callee's contract at it), so the two cannot disagree
    about a program.

    The declared path names the file only when the program reaches the file
    by it, which keeps the answer the same for every program that compiles
    the file:

    * *resolved_as* — the path the program imports the file by, when it is
      checked as a module — must be the declared path.  A file declaring
      ``module mz;`` that is imported as ``ma`` has no unambiguous own path;
    * for the entry (*resolved_as* ``None``), no module in *resolved* may
      have the path: there it names that module, as it always did.

    ``None`` for a file with no ``module`` declaration.
    """
    if program.module is None:
        return None
    declared = tuple(program.module.path)
    if resolved_as is not None:
        return declared if declared == resolved_as else None
    if any(m.path == declared for m in resolved):
        return None
    return declared
