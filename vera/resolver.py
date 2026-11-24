"""Vera module resolver — map import paths to source files.

C7a: Resolve import declarations to files on disk, parse them into
ASTs, cache results, and detect circular imports. Does NOT merge
types across modules (C7b) or enforce visibility (C7c).
"""

from __future__ import annotations

import os
import re

from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field, fields, replace
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
class _Refusal:
    """An E014 or E015 refusal, as resolution met it: its diagnostic, whose
    fix is composed after resolution from the final tables
    (:meth:`ModuleResolver._compose_fixes`), the import, its importer, the
    name its lookup found and that file's identity, and the binding it
    met (#1904)."""

    diagnostic: Diagnostic
    imp: ast.ImportDecl
    importer: Path
    entry: Path
    ident: tuple[int, int]
    bound: _Binding


#: The document's key among importers: it is read from the caller's
#: program, not by identity from a file.
_DOCUMENT = (-1, -1)

#: A repair as :meth:`ModuleResolver._walk` simulates it: an entry renamed
#: (its name, the new name, the file's identity), and imports rewritten,
#: each by its importer's key and path, to a new path.
_Rename = tuple[Path, Path, tuple[int, int]]
_Rewrites = dict[tuple[tuple[int, int], tuple[str, ...]], tuple[str, ...]]

#: What a walk of the program gives: each import by its importer's key and
#: path (as written, before a rewrite) to the file it reaches; the files
#: (by key) with an import that reaches no file; each file's identity to the
#: entries it is reached by; and the paths that name two files and the
#: files under two paths.
_Edges = dict[tuple[tuple[int, int], tuple[str, ...]], tuple[int, int]]


@dataclass(frozen=True)
class _Walk:
    edges: _Edges
    missing: frozenset[tuple[int, int]]
    entries: dict[tuple[int, int], frozenset[Path]]
    conflicts: frozenset[tuple[object, ...]]


def _name(path: Path) -> Path:
    """*path* with its directory resolved and its own name kept: a symbolic
    link is the link."""
    return path.parent.resolve() / path.name


def _module_calls(program: ast.Program, mod_path: tuple[str, ...]) -> list[str]:
    """The names *program* calls qualified by *mod_path*, sorted."""
    found: set[str] = set()
    stack: list[object] = [program]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.ModuleCall) and tuple(node.path) == mod_path:
            found.add(node.name)
        if isinstance(node, ast.Node):
            stack.extend(getattr(node, f.name) for f in fields(node))
        elif isinstance(node, (tuple, list)):
            stack.extend(node)
    return sorted(found)


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
    #: The E014 and E015 refusals, whose fixes wait for the final tables.
    _refusals: list[_Refusal] = field(default_factory=list)
    #: Each file's program by identity, as resolution read it, or as the
    #: repair check read it (None: it does not read or parse).
    _programs: dict[tuple[int, int], ast.Program | None] = field(
        default_factory=dict)
    _document: Path | None = None
    _document_imports: tuple[tuple[str, ...], ...] = ()
    _document_program: ast.Program | None = None
    _baseline: _Walk | None = None
    #: What resolution showed, which a repair may leave and nothing more:
    #: the conflicts its refusals reported, and the files whose imports it
    #: looked up (each missing import of one is an E012 it reported).
    _reported: frozenset[tuple[object, ...]] = frozenset()
    _read: frozenset[tuple[int, int]] = frozenset()

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
        self._document = file
        self._document_program = program
        self._document_imports = tuple(imp.path for imp in program.imports)
        direct = [self._resolve_single(imp, file) for imp in program.imports]
        self._compose_fixes()

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
            self._refuse(self._one_path_two_files(
                imp, importing_file, entry, by_path),
                imp, importing_file, entry, ident, by_path)
            return None
        by_file = self._file_binding.get(ident)
        if by_file is not None and by_file.path != mod_path:
            self._refuse(self._one_file_two_paths(
                imp, importing_file, file_path, by_file),
                imp, importing_file, entry, ident, by_file)
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
            self._programs[ident] = program

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

    def _refuse(
        self, diagnostic: Diagnostic, imp: ast.ImportDecl, importer: Path,
        entry: Path, ident: tuple[int, int], bound: _Binding,
    ) -> None:
        self._errors.append(diagnostic)
        self._refusals.append(
            _Refusal(diagnostic, imp, importer, entry, ident, bound))

    def _one_path_two_files(
        self, imp: ast.ImportDecl, importing_file: Path,
        entry: Path, bound: _Binding,
    ) -> Diagnostic:
        """E014: *imp* finds another file for a path the program has
        already bound (spec §8.6.2).  Its fix is composed after resolution
        (:meth:`_e014_fix`)."""
        path = self._spelled(imp.path)
        here, there = self._shown(entry), self._shown(bound.entry)
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
            # Composed after resolution, from the final tables
            # (`_e014_fix`); this is its first sentence.
            fix="Give one of the two modules another path.",
            spec_ref='Chapter 8, Section 8.6.2 "Caching"',
            severity="error",
            error_code="E014",
        )

    def _one_file_two_paths(
        self, imp: ast.ImportDecl, importing_file: Path,
        file_path: Path, bound: _Binding,
    ) -> Diagnostic:
        """E015: *imp* reaches, by another path, a file the program has
        already imported (spec §8.6.2).  Its fix is composed after
        resolution (:meth:`_e015_fix`)."""
        here, there = self._spelled(imp.path), self._spelled(bound.path)
        return Diagnostic(
            description=(
                f"'{self._shown(file_path)}' is imported by two paths: as "
                f"'{here}' in '{self._shown(importing_file)}', and as "
                f"'{there}' in '{self._shown(bound.importer)}'."
            ),
            location=self._location_from_node(imp, importing_file),
            source_line=self._source_line(importing_file, imp),
            rationale=(
                "A file is one module, under one path. Imported by two "
                "paths, it would be checked and compiled twice, as two "
                "modules, and a data type it declares would be two types "
                "that no value passes between."
            ),
            # Composed after resolution, from the final tables
            # (`_e015_fix`); this is its first sentence.
            fix="Import the file by one path everywhere.",
            spec_ref='Chapter 8, Section 8.6.2 "Caching"',
            severity="error",
            error_code="E015",
        )

    # -----------------------------------------------------------------
    # Repairs: composed after resolution, offered only when verified
    # -----------------------------------------------------------------

    def _compose_fixes(self) -> None:
        """Give each E014 and E015 its fix, now that resolution has
        finished and every binding the program makes is known (#1904).

        A concrete repair is offered only when it keeps the invariant of
        spec §8.6.2, which :meth:`_verified` checks: applied as written, the
        conflict this diagnostic reports is gone, every import the repair
        does not edit reaches the file it reached before (by identity),
        every import it edits reaches the file it reached before, and no
        import is refused that resolution did not already refuse.  It is
        composed only inside the domain where that can be
        checked without modelling links (:meth:`_in_domain`).  Elsewhere,
        and whenever composing it meets a filesystem error, the fix is the
        rule in prose, and the diagnostic is as resolution recorded it."""
        # Taken before any repair is composed: composing reads refused
        # files' programs, which resolution never read.
        self._read = frozenset(self._programs) | {_DOCUMENT}
        self._reported = frozenset(
            ("path", r.imp.path) if r.diagnostic.error_code == "E014"
            else ("file", r.bound.ident)
            for r in self._refusals)
        for refusal in self._refusals:
            e014 = refusal.diagnostic.error_code == "E014"
            try:
                fix = (self._e014_fix(refusal) if e014
                       else self._e015_fix(refusal))
            except OSError:
                fix = None
            refusal.diagnostic.fix = (
                fix if fix is not None
                else self._e014_prose(refusal) if e014
                else self._e015_prose(refusal))

    def _key(self, importer: Path) -> tuple[int, int]:
        """*importer*'s key in :meth:`_walk`: the document's, or its file's
        identity."""
        if self._document is not None and str(importer) == str(self._document):
            return _DOCUMENT
        return file_identity(importer)

    def _program_of(
        self, ident: tuple[int, int], place: Path,
    ) -> ast.Program | None:
        """The program of the file *ident*, at *place*: as resolution read
        it, else read now (a refused import's file is never read during
        resolution).  None when it does not read or parse."""
        if ident == _DOCUMENT:
            return self._document_program
        if ident not in self._programs:
            try:
                self._programs[ident] = transform(
                    parse(read_source(place), file=str(place)))
            except (SourceEncodingError, ParseError, TransformError,
                    OSError):
                self._programs[ident] = None
        return self._programs[ident]

    def _walk(
        self, rename: _Rename | None = None,
        rewrites: _Rewrites | None = None,
    ) -> _Walk:
        """Every import of every file the document reaches, a refused
        import's file included, looked up by the lookup of spec §8.6.1 from
        the directory of the file it is written in (resolved, as resolution
        looks a module's imports up), with *rename* applied to the names the
        lookups see and *rewrites* to the imports.  A filesystem error
        propagates: the caller gives the prose fix."""
        rewrites = rewrites or {}

        def find(
            mod_path: tuple[str, ...], importer: Path,
        ) -> tuple[Path, tuple[int, int]] | None:
            relative = Path(*mod_path).with_suffix(".vera")
            for place in (importer.parent / relative, self._root / relative):
                if rename is not None and _name(place) == rename[1]:
                    return place, rename[2]
                if rename is not None and _name(place) == rename[0]:
                    continue
                if place.is_file():
                    return place, file_identity(place)
            return None

        edges: _Edges = {}
        missing: set[tuple[int, int]] = set()
        entries: dict[tuple[int, int], set[Path]] = {}
        paths: dict[tuple[str, ...], set[tuple[int, int]]] = {}
        files: dict[tuple[int, int], set[tuple[str, ...]]] = {}
        seen: set[tuple[int, int]] = set()
        if self._document is None:  # resolve_imports sets it first
            return _Walk({}, frozenset(), {}, frozenset())
        queue = [(_DOCUMENT, self._document, self._document_imports)]
        while queue:
            key, importer, imports = queue.pop(0)
            for written in imports:
                path = rewrites.get((key, written), written)
                hit = find(path, importer)
                if hit is None:
                    missing.add(key)
                    continue
                place, ident = hit
                edges[(key, written)] = ident
                entries.setdefault(ident, set()).add(place)
                paths.setdefault(path, set()).add(ident)
                files.setdefault(ident, set()).add(path)
                if ident in seen:
                    continue
                seen.add(ident)
                # A renamed file's program is read before the walk, from
                # its old name (`_e014_fix`); every other is read here.
                program = self._program_of(ident, place)
                # A renamed file's new name does not exist; resolving it
                # resolves its directory and keeps the name.
                queue.append((ident, place.resolve(), tuple(
                    imp.path for imp in program.imports) if program else ()))
        conflicts: set[tuple[object, ...]] = {
            ("path", p) for p, s in paths.items() if len(s) > 1}
        conflicts |= {("file", f) for f, s in files.items() if len(s) > 1}
        return _Walk(edges, frozenset(missing),
                     {i: frozenset(e) for i, e in entries.items()},
                     frozenset(conflicts))

    def _base(self) -> _Walk:
        if self._baseline is None:
            self._baseline = self._walk()
        return self._baseline

    def _verified(
        self, conflict: tuple[object, ...], rename: _Rename | None,
        rewrites: _Rewrites,
    ) -> bool:
        """Whether the repair keeps the invariant of spec §8.6.2: the
        conflict is gone; every import, edited or not, reaches the file it
        reached before (so none that found a file finds none); and no
        import is refused that resolution did not already refuse.

        The walk reads further than resolution did: a refused import's
        file, and the files it imports.  A repair makes resolution read
        them, so the comparison of files reached covers them, but what the
        repair may leave is only what resolution SHOWED: a conflict one of
        its refusals reported, and an import finding no file in a file it
        read (an E012 it reported).  A conflict or a missing import met
        only through a refused import would be refused for the first time
        once the repair is applied (#1904)."""
        base, after = self._base(), self._walk(rename, rewrites)
        if conflict in after.conflicts:
            return False
        if after.edges != base.edges:
            return False
        if any(key not in self._read for key in after.missing):
            return False
        return after.conflicts <= self._reported  # pragma: no mutate (< is equivalent: the refusal's own conflict is in _reported and not in after)

    def _in_domain(self, ident: tuple[int, int]) -> bool:
        """Whether a repair of the file *ident* can be checked without
        modelling links: every entry any import of the program reaches it
        by is a plain file under its own name, with no second hard link
        and no spelling that differs only in case.  A file NOT in play may
        be a link, or have a second hard link: that is outside this test."""
        for entry in self._base().entries.get(ident, frozenset()):
            if entry.is_symlink() or os.stat(entry).st_nlink != 1:
                return False
            if entry.name not in os.listdir(entry.parent):
                return False
        return True

    def _call_edits(
        self, key: tuple[int, int], importer: Path, old: tuple[str, ...],
        new: tuple[str, ...],
    ) -> str | None:
        """The sentence naming each qualified call in *importer* by the old
        path, written by the new; "" when there is none; None when the
        importer's program cannot be read, so the calls cannot be named."""
        program = self._program_of(key, importer)
        if program is None:
            return None
        calls = _module_calls(program, old)
        if not calls:
            return ""
        was, now = self._spelled(old), self._spelled(new)
        return (f" In '{self._shown(importer)}', write "
                + ", and ".join(f"`{now}::{c}` in place of `{was}::{c}`"
                                for c in calls) + ".")

    #: The guarantee a concrete repair carries, said where it is offered.
    _GUARANTEE = (
        " Applied as written, this clears this conflict, every other "
        "import reaches the file it reaches now, and no import is refused "
        "that is not refused now. It is about imports, not errors: a "
        "module this lets an import bind, and each call into it, may show "
        "errors of its own.")

    def _e014_fix(self, refusal: _Refusal) -> str | None:
        """Rename the file this import found, beside itself, and change the
        import: the first name, of *path* suffixed 2 to 99 then
        ``_renamed``, that :meth:`_verified` passes; None outside the
        domain or where the calls cannot be named (the prose fix)."""
        imp, entry = refusal.imp, refusal.entry
        old = imp.path
        if not self._in_domain(refusal.ident):
            return None
        here = self._shown(entry)
        key = self._key(refusal.importer)
        program = self._program_of(refusal.ident, entry)
        names = [f"{old[-1]}{n}" for n in range(2, 100)]
        for last in [*names, f"{old[-1]}_renamed"]:
            renamed = entry.with_name(last + entry.suffix)
            # A file at the new name would be replaced by the rename.  The
            # walk sees only files some import reaches, so a file no
            # import reaches is ruled out here.
            if os.path.lexists(renamed):
                continue
            new = (*old[:-1], last)
            if not self._verified(
                    ("path", old), (_name(entry), _name(renamed), refusal.ident),
                    {(key, old): new}):
                continue
            calls = self._call_edits(key, refusal.importer, old, new)
            if calls is None:
                return None
            return (
                f"Give one of the two modules another path: rename "
                f"`{here}` to `{self._shown(renamed)}` and write "
                f"`import {self._spelled(new)}` here in place of "
                f"`import {self._spelled(old)}`."
                + calls + self._own_path_edits(program, old, new, renamed)
                + self._GUARANTEE)
        return (
            f"Give one of the two modules another path. No rename of "
            f"`{here}` to `{old[-1]}2` through `{old[-1]}99`, or to "
            f"`{old[-1]}_renamed`, with this import changed to match, "
            f"clears the conflict and leaves every other import reaching "
            f"the file it reaches now, so rename `{here}` or "
            f"`{self._shown(refusal.bound.entry)}` to a name no file and no "
            f"module of the program takes, and change its imports to match."
        )

    def _e014_prose(self, refusal: _Refusal) -> str:
        here = self._shown(refusal.entry)
        there = self._shown(refusal.bound.entry)
        return (
            f"Give one of the two modules another path: rename `{here}` or "
            f"`{there}` to a name no file and no module of the program "
            f"takes, and change each import of it, and each qualified call "
            f"by its old path, to match, so that every other import still "
            f"reaches the file it reaches now. A repair is not composed "
            f"here: a symbolic link, a second hard link or a spelling that "
            f"differs only in case reaches the file, or the files could not "
            f"be read."
        )

    def _own_path_edits(
        self, program: ast.Program | None, old: tuple[str, ...],
        new: tuple[str, ...], renamed: Path,
    ) -> str:
        """The edits a renamed file needs where it names itself by its old
        path: its ``module`` declaration and its self-qualified calls
        (spec §8.2, §8.5.3), which the lookups cannot see."""
        if (program is None or program.module is None
                or tuple(program.module.path) != old):
            return ""
        was, now = self._spelled(old), self._spelled(new)
        edits = [f"`module {now};` in place of `module {was};`"]
        edits += [f"`{now}::{name}` in place of `{was}::{name}`"
                  for name in _module_calls(program, old)]
        return (f" In `{self._shown(renamed)}`, write "
                + ", and ".join(edits) + ".")

    def _e015_fix(self, refusal: _Refusal) -> str | None:
        """Import the file by one path everywhere: this import changed to
        the other's path, else the other changed to this one's; the first
        that :meth:`_verified` passes.  None outside the domain or where
        the calls cannot be named (the prose fix)."""
        imp, bound = refusal.imp, refusal.bound
        here, there = self._spelled(imp.path), self._spelled(bound.path)
        shown = self._shown(refusal.entry.resolve())
        other = self._shown(bound.importer)
        if not self._in_domain(bound.ident):
            return None
        mine, theirs = self._key(refusal.importer), self._key(bound.importer)
        conflict = ("file", bound.ident)
        if self._verified(conflict, None, {(mine, imp.path): bound.path}):
            calls = self._call_edits(
                mine, refusal.importer, imp.path, bound.path)
            if calls is None:
                return None
            return (
                f"Import `{shown}` by one path everywhere: write "
                f"`import {there}` here in place of `import {here}`, the "
                f"path '{other}' imports it by, which reaches it from this "
                f"file too." + calls + self._GUARANTEE
            )
        if self._verified(conflict, None, {(theirs, bound.path): imp.path}):
            calls = self._call_edits(
                theirs, bound.importer, bound.path, imp.path)
            if calls is None:
                return None
            return (
                f"Import `{shown}` by one path everywhere: write "
                f"`import {here}` in '{other}' in place of "
                f"`import {there}`, the path this file imports it by, "
                f"which reaches it from there too." + calls + self._GUARANTEE
            )
        return (
            f"Import `{shown}` by one path everywhere. Neither '{here}' "
            f"nor '{there}', written in the other file, reaches it there "
            f"and leaves every other import reaching the file it reaches "
            f"now, so move it to a directory both files reach by one path, "
            f"such as the project root, and import it by that path in both."
        )

    def _e015_prose(self, refusal: _Refusal) -> str:
        shown = self._shown(refusal.entry.resolve())
        return (
            f"Import `{shown}` by one path everywhere: choose one path that "
            f"reaches it from '{self._shown(refusal.importer)}' and from "
            f"'{self._shown(refusal.bound.importer)}', and write it in both "
            f"imports, and in each qualified call by the other path, so "
            f"that every other import still reaches the file it reaches "
            f"now. A repair is not composed here: a symbolic link, a second "
            f"hard link or a spelling that differs only in case reaches the "
            f"file, or the files could not be read."
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
