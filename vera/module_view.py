"""What one namespace can see through its imports — ONE derivation.

A Vera program is a set of namespaces: the entry file, and every module the
resolver reached.  What a declaration in one of them may NAME is decided by
that namespace's own ``import`` list — spec §8.6.4 makes visibility a property
of the importer, not of the module — and both the checker and code generation
need the answer for every module, not only for the entry file: the checker to
register a module's signatures and to check its bodies, code generation to
measure the WASM width of every type those signatures name.

Each used to answer it separately.  The checker registered a module's
declarations with none of the module's own imports in scope, so a data type
the module imported fell through to an opaque placeholder (#1489); code
generation registered them the same way, so the same type came out with no
WASM representation and a direct ``match`` on the module's result dropped its
caller (#1493).  The import list itself was keyed by path with the last
statement winning, so ``import m(a); import m(b);`` admitted ``b`` alone.

Three functions, each the only place its question is answered:

* :func:`import_filters` — per imported path, the names a namespace admits:
  the UNION over every ``import`` of that path, ``None`` for a wildcard.
* :func:`modules_visible_to` — the resolved modules a namespace can reach,
  with ``direct`` re-derived against its own import list.
* :func:`imported_data_types` — which module each data type name a namespace
  imports comes from.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import replace

from vera import ast
from vera.resolver import ResolvedModule

__all__ = [
    "import_filters",
    "imported_data_types",
    "modules_visible_to",
]


def import_filters(
    imports: Iterable[ast.ImportDecl],
) -> dict[tuple[str, ...], set[str] | None]:
    """One filter per imported PATH, unioned across repeated imports.

    A namespace may name a declaration that ANY of its import lists admits,
    so two statements naming one module contribute the union of their lists
    and a wildcard dominates every list beside it.  Keying a dict on the path
    instead made the LAST statement win and discarded the others: with
    ``import m(a); import m(b);`` the surviving filter admits ``b`` alone.

    Repeating one statement adds nothing, so the result is idempotent in
    the repetition.  Paths keep their first-appearance order, which is the
    order every consumer walks them in.
    """
    out: dict[tuple[str, ...], set[str] | None] = {}
    for imp in imports:
        path = tuple(imp.path)
        names = set(imp.names) if imp.names is not None else None
        if path not in out:
            out[path] = names
            continue
        existing = out[path]
        if existing is None or names is None:
            out[path] = None  # a wildcard admits everything
        else:
            out[path] = existing | names
    return out


def modules_visible_to(
    program: ast.Program, resolved: Sequence[ResolvedModule],
) -> list[ResolvedModule]:
    """The resolved modules *program* can reach, re-scoped to *program*.

    The same objects the entry resolved, with ``direct`` recomputed against
    *program*'s own import list: what is transitive from the entry may be a
    direct import here, and §8.6.4 visibility is a property of the importer,
    not of the module.  A path the entry never resolved is skipped — the
    resolver reaches every transitive import, so a missing one did not
    resolve, and a name it would have supplied then misses loudly rather than
    binding something else.

    Walked in import order, so the list is a function of the source alone.
    """
    by_path = {m.path: m for m in resolved}
    direct = [path for path in import_filters(program.imports)
              if path in by_path]
    direct_set = set(direct)
    out: list[ResolvedModule] = []
    seen: set[tuple[str, ...]] = set()
    frontier = list(reversed(direct))
    while frontier:
        path = frontier.pop()
        if path in seen:
            continue
        seen.add(path)
        dep = by_path[path]
        out.append(replace(dep, direct=path in direct_set))
        frontier.extend(reversed([
            p for p in import_filters(dep.program.imports) if p in by_path
        ]))
    return out


def imported_data_types(
    program: ast.Program,
    modules: Mapping[tuple[str, ...], ast.Program],
) -> dict[str, tuple[tuple[str, ...], ...]]:
    """Each data type name *program* imports, with every module supplying it.

    A name is imported when a module *program* imports DIRECTLY declares it
    ``public`` and *program*'s filter for that module admits it
    (:func:`import_filters`).  Suppliers are listed in import order.  A module
    *program* imports that is not in *modules* did not resolve, and supplies
    nothing.

    A name with two suppliers denotes no one declaration (spec §8.5.2.2), and
    what that means is each consumer's to say: the checker refuses it (E156)
    and binds it to neither, while code generation, the backstop behind that
    refusal, still knows the name is a data type.

    Every namespace is asked the same question this way — the entry file and
    each module, by the checker registering a module's signatures and by code
    generation measuring them and compiling its bodies — so they cannot
    disagree about which data types a module's declarations may name.
    """
    suppliers: dict[str, list[tuple[str, ...]]] = {}
    for path, name_filter in import_filters(program.imports).items():
        dep = modules.get(path)
        if dep is None:
            continue
        for tld in dep.declarations:
            decl = tld.decl
            if not isinstance(decl, ast.DataDecl):
                continue
            if (tld.visibility or "private") != "public":
                continue
            if name_filter is not None and decl.name not in name_filter:
                continue
            owners = suppliers.setdefault(decl.name, [])
            if path not in owners:
                owners.append(path)
    return {name: tuple(owners) for name, owners in suppliers.items()}
