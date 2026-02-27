"""Vera module resolver — map import paths to source files.

C7a: Resolve import declarations to files on disk, parse them into
ASTs, cache results, and detect circular imports. Does NOT merge
types across modules (C7b) or enforce visibility (C7c).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.parser import parse_file
from vera.transform import transform


@dataclass(frozen=True)
class ResolvedModule:
    """A resolved and parsed module."""

    path: tuple[str, ...]  # e.g., ("vera", "math")
    file_path: Path  # absolute path to the .vera file
    program: ast.Program  # parsed + transformed AST
    source: str  # raw source text


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
        """Resolve all imports in a program.

        Returns a list of successfully resolved modules.
        Errors are accumulated in ``self.errors``.
        """
        resolved: list[ResolvedModule] = []
        for imp in program.imports:
            mod = self._resolve_single(imp, file)
            if mod is not None:
                resolved.append(mod)
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
                    location=self._location_from_node(imp),
                    rationale=(
                        "Circular imports are not allowed. Restructure "
                        "the modules to break the dependency cycle."
                    ),
                    severity="error",
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
                    location=self._location_from_node(imp),
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
                    severity="error",
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
        except Exception as exc:
            self._errors.append(
                Diagnostic(
                    description=(
                        f"Error parsing imported module "
                        f"'{'.'.join(mod_path)}': {exc}"
                    ),
                    location=self._location_from_node(imp),
                    severity="error",
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
    def _location_from_node(node: ast.Node) -> SourceLocation:
        """Extract a SourceLocation from an AST node's span."""
        if node.span:
            return SourceLocation(
                line=node.span.line,
                column=node.span.column,
            )
        return SourceLocation()
