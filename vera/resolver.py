"""Vera module resolver — map import paths to source files.

C7a: Resolve import declarations to files on disk, parse them into
ASTs, cache results, and detect circular imports. Does NOT merge
types across modules (C7b) or enforce visibility (C7c).
"""

from __future__ import annotations

import os
import re

from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field, replace
from pathlib import Path

from vera import ast
from vera.errors import (
    Diagnostic,
    ParseError,
    SourceEncodingError,
    SourceLocation,
    TransformError,
    source_lines,
)
from vera.parser import parse, read_source
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
    #: The importing files (``str`` of each one's ``Path``) whose import of
    #: this path the resolver refused (#1904): the import binds nothing,
    #: though another importer's import of the path bound this module.  A
    #: module's own refused imports are already dropped from its
    #: ``program``; the document's are dropped by :func:`accepted_imports`.
    refused_by: frozenset[str] = frozenset()


#: A name one part of a module path can be (the grammar's ``LOWER_IDENT``).
_MODULE_NAME = re.compile(r"[a-z][a-zA-Z0-9_]*")


def file_identity(path: Path) -> tuple[int, int]:
    """The identity of the file at *path*: its device and file number,
    as the filesystem gives them (``os.stat``'s ``st_dev`` and
    ``st_ino``), which is how :func:`os.path.samefile` decides that two
    names are one file.

    Two names are one module file exactly when the filesystem says they
    are one file (#1904): a symbolic link and its target, two hard links,
    and on a filesystem that compares names without case (macOS's default,
    Windows), two spellings that differ only in case.  Comparing the names
    themselves, even resolved, gets the last two wrong.  On Windows,
    ``os.stat`` fills both fields from the file's volume serial number and
    file index, which is what ``samefile`` reads there too.
    """
    st = os.stat(path)
    return (st.st_dev, st.st_ino)


@dataclass(frozen=True)
class _Binding:
    """One module path bound to one file in a program, and the file whose
    import bound them (#1904)."""

    path: tuple[str, ...]
    ident: tuple[int, int]
    file: Path
    importer: Path
    #: The name the importer's lookup found (a symbolic link stays a link):
    #: the file a fix renames.
    entry: Path


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
    #: The files being resolved, by identity (:func:`file_identity`), so a
    #: cycle is seen at the first import that re-enters a file, whatever
    #: path that import spells it by.
    _in_progress: set[tuple[int, int]] = field(default_factory=set)
    _errors: list[Diagnostic] = field(default_factory=list)
    #: A module path → the file it names in this program, and the file
    #: whose import bound it (#1904): a path names one file.
    _path_binding: dict[tuple[str, ...], _Binding] = field(
        default_factory=dict,
    )
    #: A file, by identity → the path it is imported by, and the file whose
    #: import bound it: a file is one module, under one path.
    _file_binding: dict[tuple[int, int], _Binding] = field(
        default_factory=dict,
    )
    #: The files that did not decode, by identity: each is read, and its
    #: E024 reported, once.
    _undecodable: set[tuple[int, int]] = field(default_factory=set)
    _unread: dict[tuple[Path, tuple[str, ...]], Path] = field(
        default_factory=dict,
    )
    #: Each refused import, by its importing file (``str`` of its ``Path``)
    #: and module path: whatever another importer bound the path to, this
    #: import binds nothing (#1904).
    _refused: set[tuple[str, tuple[str, ...]]] = field(default_factory=set)

    @property
    def errors(self) -> list[Diagnostic]:
        """Accumulated resolution diagnostics."""
        return list(self._errors)

    @property
    def unread(self) -> dict[tuple[Path, tuple[str, ...]], Path]:
        """Each import whose file the resolver found and could not read as
        UTF-8 (its E024), by the importing file and the module path, with
        the file it found: the binding a module that resolved has in its
        ``file_path``, for one that did not.  A module that does not read
        is not cached, so each importer resolves it again, from its own
        directory, and has its own entry."""
        return dict(self._unread)

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
        # A direct import is one this program's own import resolved to: an
        # import the resolver refused binds nothing, whatever module another
        # importer bound its path to (#1904).
        direct = [self._resolve_single(imp, file) for imp in program.imports]

        # Assemble the closure.  Emit direct imports (in source order) first,
        # then the transitive-only modules from the cache, deduplicated by
        # path so a diamond (two importers of one base) yields the base once.
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

        for mod in direct:
            if mod is not None:
                _emit(mod, direct=True)
        for mod in self._cache.values():
            _emit(mod, direct=False)

        # A refused import of a path the program still binds (another
        # importer's import of it was accepted) binds nothing for its own
        # importer: dropped from a module's program here, and marked on the
        # module for the document's (:func:`accepted_imports`).  Every later
        # stage reads visibility from a program's import list by path, so
        # this is the one place the refusal can be kept (#1904).
        emitted = {mod.path for mod in resolved}
        refused = {(f, p) for f, p in self._refused if p in emitted}
        return [self._as_accepted(mod, refused) for mod in resolved]

    def _as_accepted(
        self, mod: ResolvedModule,
        refused: set[tuple[str, tuple[str, ...]]],
    ) -> ResolvedModule:
        own = str(mod.file_path)
        drop = {p for f, p in refused if f == own}
        by = frozenset(f for f, p in refused if p == mod.path)
        if not drop and not by:
            return mod
        program = mod.program
        if drop:
            program = replace(program, imports=tuple(
                imp for imp in program.imports if imp.path not in drop))
        return replace(mod, program=program, refused_by=by)

    # -----------------------------------------------------------------
    # Internal
    # -----------------------------------------------------------------

    def _resolve_single(
        self,
        imp: ast.ImportDecl,
        importing_file: Path,
    ) -> ResolvedModule | None:
        """Resolve a single import declaration.

        Returns the ResolvedModule, or None on failure (error recorded, and
        the import recorded as refused: it binds nothing).
        """
        mod = self._resolve_one(imp, importing_file)
        if mod is None:
            self._refused.add((str(importing_file), imp.path))
        return mod

    def _resolve_one(
        self,
        imp: ast.ImportDecl,
        importing_file: Path,
    ) -> ResolvedModule | None:
        mod_path = imp.path

        # Look the path up from THIS importer first (spec §8.6.1), so the
        # file it names is the importer's own, whatever an earlier import
        # of the same path found (#1904).
        entry = self._lookup(mod_path, importing_file)
        if entry is None:
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
        try:
            file_path = entry.resolve()
            ident = file_identity(file_path)
        except OSError as exc:
            # Found, and gone or unreadable before it could be identified:
            # the import cannot read it, as a failed read below is E013.
            self._errors.append(self._unreadable(imp, importing_file, exc))
            return None

        # Circular import detection, by the file: a cycle through two
        # spellings of one file is a cycle.
        if ident in self._in_progress:
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

        # A path names one file in a program, and a file is one module
        # under one path (spec §8.6.2, #1904).
        by_path = self._path_binding.get(mod_path)
        if by_path is not None and by_path.ident != ident:
            self._errors.append(self._one_path_two_files(
                imp, importing_file, entry, by_path))
            return None
        by_file = self._file_binding.get(ident)
        if by_file is not None and by_file.path != mod_path:
            self._errors.append(self._one_file_two_paths(
                imp, importing_file, file_path, by_file))
            return None

        if mod_path in self._cache:
            return self._cache[mod_path]
        if ident in self._undecodable:
            # Read once and reported once; this import is placed by its
            # record (#1788).
            self._unread[(importing_file, mod_path)] = file_path
            return None

        binding = _Binding(mod_path, ident, file_path, importing_file, entry)
        self._path_binding.setdefault(mod_path, binding)
        self._file_binding.setdefault(ident, binding)

        # Mark as in-progress (circular detection)
        self._in_progress.add(ident)

        try:
            # Read once, then parse and transform
            source = read_source(file_path)
            tree = parse(source, file=str(file_path))
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
        except SourceEncodingError as exc:
            # The module's bytes are not UTF-8: its own E024, located in the
            # module at the byte, not an E013 at the import (#1666).
            self._errors.append(exc.diagnostic)
            self._unread[(importing_file, mod_path)] = file_path
            self._undecodable.add(ident)
            return None
        except (ParseError, TransformError, OSError) as exc:
            # Only genuine resolution failures of the imported file become
            # E013: ParseError/TransformError from parse/transform, and
            # OSError from the read.  Any other exception is an internal
            # compiler bug and must propagate, not be relabeled as the
            # user's module failing to parse.
            self._errors.append(self._unreadable(imp, importing_file, exc))
            return None
        finally:
            self._in_progress.discard(ident)

    def _unreadable(
        self, imp: ast.ImportDecl, importing_file: Path, exc: Exception,
    ) -> Diagnostic:
        """E013: the file *imp* found could not be read, parsed or
        transformed."""
        mod_path = imp.path
        return Diagnostic(
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
        )

    def _shown(self, path: Path) -> str:
        """*path* as a diagnostic names it: relative to the project root
        when it lies under it, in ``/`` form on every platform.  Its
        directory is resolved and its own name is not, so a symbolic link
        is shown as the link, the name the lookup found."""
        try:
            return (path.parent.resolve() / path.name).relative_to(
                self._root.resolve()).as_posix()
        except ValueError:
            return path.as_posix()

    def _spelled(self, mod_path: tuple[str, ...]) -> str:
        return ".".join(mod_path)

    def _one_path_two_files(
        self, imp: ast.ImportDecl, importing_file: Path,
        entry: Path, bound: _Binding,
    ) -> Diagnostic:
        """E014: *imp* finds another file for a path the program has
        already bound (spec §8.6.2)."""
        path = self._spelled(imp.path)
        here, there = self._shown(entry), self._shown(bound.entry)
        renamed = self._free_path(imp.path, entry, importing_file)
        if renamed is None:
            fix = (
                f"Give one of the two modules another path. No name from "
                f"`{imp.path[-1]}2` to `{imp.path[-1]}99`, nor "
                f"`{imp.path[-1]}_renamed`, is free beside `{here}` and "
                f"reached from this file by its own lookup, so rename "
                f"`{here}` or `{there}` to a name no file and no module of "
                f"the program takes, and change its import to match."
            )
        else:
            new_file = self._shown(entry.with_name(renamed[-1] + entry.suffix))
            fix = (
                f"Give one of the two modules another path. Rename "
                f"`{here}` to `{new_file}` and write "
                f"`import {self._spelled(renamed)}` here in place of "
                f"`import {path}`; or rename `{there}` and change the "
                f"import of it in '{self._shown(bound.importer)}' the same "
                f"way."
            )
        return Diagnostic(
            description=(
                f"Module path '{path}' names two files in this program: "
                f"'{self._shown(importing_file)}' imports '{path}' as "
                f"'{here}', and '{self._shown(bound.importer)}' imports it "
                f"as '{there}'."
            ),
            location=self._location_from_node(imp, importing_file),
            source_line=self._source_line(importing_file, imp),
            rationale=(
                "A module path names one module in a program. Every stage "
                "links a module by its path, so two files under one path "
                "cannot both be compiled, and taking either one would run a "
                "module that the other import does not name."
            ),
            fix=fix,
            spec_ref='Chapter 8, Section 8.6.2 "Caching"',
            severity="error",
            error_code="E014",
        )

    def _root_path(self, file_path: Path) -> tuple[str, ...] | None:
        """*file_path*'s module path from the project root, if it lies
        under the root and each part is a name a module path can hold."""
        try:
            rel = file_path.resolve().relative_to(self._root.resolve())
        except ValueError:
            return None
        # A file under the root has at least its own name as a part.
        parts = rel.with_suffix("").parts
        if all(_MODULE_NAME.fullmatch(p) for p in parts):
            return tuple(parts)
        return None

    def _free_path(
        self, mod_path: tuple[str, ...], entry: Path, importing_file: Path,
    ) -> tuple[str, ...] | None:
        """A path for *entry*, renamed beside itself, that no file takes
        yet, that no module of the program is bound to, and that the
        importer's lookup would find at the renamed entry: *mod_path* with
        its last name suffixed by 2 to 99, else by ``_renamed``; None when
        none of them is."""
        names = [f"{mod_path[-1]}{n}" for n in range(2, 100)]
        for last in [*names, f"{mod_path[-1]}_renamed"]:
            candidate = (*mod_path[:-1], last)
            renamed = entry.with_name(last + entry.suffix)
            if (not os.path.lexists(renamed)
                    and candidate not in self._path_binding
                    and self._finds(candidate, importing_file, renamed)):
                return candidate
        return None

    def _finds(
        self, mod_path: tuple[str, ...], importing_file: Path, target: Path,
    ) -> bool:
        """Whether the lookup of *mod_path* from *importing_file* (spec
        §8.6.1) would stop at *target*, a name that does not exist yet:
        each place it looks, in order, until one holds a file."""
        relative = Path(*mod_path).with_suffix(".vera")
        want = target.parent.resolve() / target.name
        for place in (importing_file.parent / relative, self._root / relative):
            if place.parent.resolve() / place.name == want:
                return True
            if place.is_file():
                return False
        # Unreached: the renamed entry is one of the lookup's places, the
        # importer's directory or the root, as the entry itself is.
        return False  # pragma: no mutate

    def _one_file_two_paths(
        self, imp: ast.ImportDecl, importing_file: Path,
        file_path: Path, bound: _Binding,
    ) -> Diagnostic:
        """E015: *imp* reaches, by another path, a file the program has
        already imported (spec §8.6.2)."""
        here, there = self._spelled(imp.path), self._spelled(bound.path)
        shown = self._shown(file_path)
        other = self._shown(bound.importer)
        ident = bound.ident

        def reaches(mod_path: tuple[str, ...], importer: Path) -> bool:
            # A file that cannot be identified is not offered: the fix
            # names only an import it has checked (#1904).
            found = self._lookup(mod_path, importer)
            try:
                return found is not None and file_identity(found) == ident
            except OSError:
                return False

        if reaches(bound.path, importing_file):
            fix = (
                f"Import `{shown}` by one path everywhere: write "
                f"`import {there}` here in place of `import {here}`, the "
                f"path '{other}' imports it by, which reaches it from this "
                f"file too."
            )
        elif reaches(imp.path, bound.importer):
            fix = (
                f"Import `{shown}` by one path everywhere: write "
                f"`import {here}` in '{other}' in place of "
                f"`import {there}`, the path this file imports it by, "
                f"which reaches it from there too."
            )
        elif (rooted := self._root_path(file_path)) is not None and (
                reaches(rooted, importing_file)
                and reaches(rooted, bound.importer)):
            fix = (
                f"Import `{shown}` by one path everywhere: its path from "
                f"the project root, '{self._spelled(rooted)}', reaches it "
                f"from both files, so write `import "
                f"{self._spelled(rooted)}` here in place of `import {here}`"
                f" and in '{other}' in place of `import {there}`."
            )
        else:
            fix = (
                f"Import `{shown}` by one path everywhere. Neither "
                f"'{here}' nor '{there}' reaches it from both files by the "
                f"lookup of spec section 8.6.1 (the importing file's "
                f"directory, then the project root), so move it to a "
                f"directory both files reach by one path, such as the "
                f"project root, and import it by that path in both."
            )
        return Diagnostic(
            description=(
                f"'{shown}' is imported by two paths: as '{here}' in "
                f"'{self._shown(importing_file)}', and as '{there}' in "
                f"'{other}'."
            ),
            location=self._location_from_node(imp, importing_file),
            source_line=self._source_line(importing_file, imp),
            rationale=(
                "A file is one module, under one path. Imported by two "
                "paths, it would be checked and compiled twice, as two "
                "modules, and a data type it declares would be two types "
                "that no value passes between."
            ),
            fix=fix,
            spec_ref='Chapter 8, Section 8.6.2 "Caching"',
            severity="error",
            error_code="E015",
        )

    def _lookup(
        self,
        mod_path: tuple[str, ...],
        importing_file: Path,
    ) -> Path | None:
        """The name the lookup of spec §8.6.1 finds for *mod_path* from
        *importing_file*, unresolved (a symbolic link stays a link)."""
        relative = Path(*mod_path).with_suffix(".vera")

        # Try relative to importing file's directory
        candidate = importing_file.parent / relative
        if candidate.is_file():
            return candidate

        # Try relative to the project root
        root_candidate = self._root / relative
        if root_candidate.is_file():
            return root_candidate

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
            # The text the parser saw: a leading byte-order mark is no
            # part of line 1, as the node's column counts it (#1790).
            lines = source_lines(read_source(importing_file))
        except (OSError, SourceEncodingError):
            return ""
        idx = node.span.line - 1
        return lines[idx] if 0 <= idx < len(lines) else ""


def accepted_imports(
    program: ast.Program, file: str | Path | None,
    modules: Sequence[ResolvedModule],
) -> ast.Program:
    """*program*, the document at *file*, without the imports the resolver
    refused while another importer's import of the same path bound a module
    (#1904): a refused import binds nothing, and every later stage reads a
    program's visibility from its import list by path."""
    if file is None:
        return program
    own = str(Path(file))
    drop = {m.path for m in modules if own in m.refused_by}
    if not drop:
        return program
    return replace(program, imports=tuple(
        imp for imp in program.imports if imp.path not in drop))


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
