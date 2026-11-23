"""A module path names one file in a program, and a file is one module
under one path (#1904, spec §8.6.2).

The resolver looked an import up by its path in a cache before it looked
for the importer's own file, so the first import of a path decided the file
for every importer (`vera run` printed `22` or `11` by import order where
each import's own lookup, §8.6.1, gives `12`), and a file imported by two
paths was read, checked and compiled twice, as two modules, its data types
split in two.  Each import is now looked up from its own file, and the
resolver refuses a program whose lookups bind one path to two files
(**E014**) or one file to two paths (**E015**), at the import that meets the
conflict.

The class, by enumeration:

* the layout of the two importers: the document itself and a module in a
  subdirectory (`root`), two modules in sibling subdirectories
  (`siblings`), and a module two directories deep beside one in another
  subdirectory (`nested`);
* which importer resolves first: the order of the document's imports;
* the relation: one path and two files, two paths and one file, and the
  plain case of one path and one file reached from both;
* the command: `vera check`, `vera verify` and `vera run`, and the language
  server's published diagnostics.

Whether a program is refused, and with which code, is asserted to be the
same in both orders; the text is asserted to name both importers and both
files (or both paths), whichever was resolved first.
"""

from __future__ import annotations

import json
import os
import pathlib
import re

import pytest

from tests import pipeline
from vera.lsp.features import analyze, to_lsp_diagnostics
from vera.obligations.session import VerificationSession

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of its parametrised cells, and all of them when it changes this file or a
# module that decides a module's identity: the resolver, and the server's
# placement of a module's diagnostics.
pytestmark = pytest.mark.matrix(decides=[
    "vera/resolver.py",
    "vera/lsp/features.py",
])

HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def fn(name: str, body: str) -> str:
    return f"public fn {name}(@Unit -> @Int)\n{HDR}{{\n  {body}\n}}\n"


def main_fn(calls: list[str]) -> str:
    prints = ";\n  ".join(f"IO.print(int_to_string({c}))" for c in calls)
    return ("public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
            f"  effects(<IO>)\n{{\n  {prints}\n}}\n")


def write(root: pathlib.Path, rel: str, text: str | bytes) -> pathlib.Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(text, bytes):
        path.write_bytes(text)
    else:
        path.write_text(text, encoding="utf-8")
    return path


def module_path(rel: str) -> str:
    """`a/b/p.vera` -> `a.b.p`."""
    return ".".join(pathlib.PurePosixPath(rel).with_suffix("").parts)


#: Each layout's two importers, P and Q, as files under the project root;
#: `None` for P means the document (`main.vera`) imports the target itself.
LAYOUTS: dict[str, tuple[str | None, str]] = {
    "root": (None, "b/q.vera"),
    "siblings": ("a/p.vera", "b/q.vera"),
    "nested": ("a/b/p.vera", "c/q.vera"),
}


def build(tmp: pathlib.Path, layout: str, relation: str,
          q_first: bool) -> tuple[pathlib.Path, str]:
    """The program for one cell: the entry's path and its text.

    *relation* `one_path_two_files`: P and Q each import `lib`, which each
    finds beside it (`word` returns 1 beside P and 2 beside Q).
    `two_paths_one_file`: Q imports the `lib.vera` beside it as `lib`, and P
    imports the same file by its path from the root (P's directory holds no
    such file, so the lookup falls through to the root).  `plain`: both
    import `shared`, which only the root holds.
    """
    p_rel, q_rel = LAYOUTS[layout]
    q_dir = pathlib.PurePosixPath(q_rel).parent
    if relation == "one_path_two_files":
        p_dir = pathlib.PurePosixPath(p_rel).parent if p_rel else pathlib.PurePosixPath(".")
        write(tmp, (p_dir / "lib.vera").as_posix(), "module lib;\n\n" + fn("word", "1"))
        write(tmp, (q_dir / "lib.vera").as_posix(), "module lib;\n\n" + fn("word", "2"))
        p_imp = q_imp = "lib"
    elif relation == "two_paths_one_file":
        write(tmp, (q_dir / "lib.vera").as_posix(), "module lib;\n\n" + fn("word", "2"))
        q_imp = "lib"
        p_imp = module_path((q_dir / "lib.vera").as_posix())
    else:
        write(tmp, "shared.vera", "module shared;\n\n" + fn("word", "1"))
        p_imp = q_imp = "shared"
    write(tmp, q_rel, f"module {module_path(q_rel)};\n\nimport {q_imp}(word);\n\n"
          + fn("wq", "word(())"))
    q_line = f"import {module_path(q_rel)}(wq);"
    if p_rel is None:
        p_line = f"import {p_imp}(word);"
        p_call = "word(())"
    else:
        write(tmp, p_rel, f"module {module_path(p_rel)};\n\nimport {p_imp}(word);\n\n"
              + fn("wp", "word(())"))
        p_line = f"import {module_path(p_rel)}(wp);"
        p_call = "wp(())"
    imports = [q_line, p_line] if q_first else [p_line, q_line]
    main = "\n".join(imports) + "\n\n" + main_fn([p_call, "wq(())"])
    return write(tmp, "main.vera", main), main


def check_json(path: pathlib.Path, command: str = "check") -> list[dict]:
    out = pipeline.cli(command, "--json", path).stdout
    return json.loads(out)["diagnostics"]


CODE = {"one_path_two_files": "E014", "two_paths_one_file": "E015", "plain": None}


@pytest.mark.parametrize("q_first", [False, True], ids=["p_first", "q_first"])
@pytest.mark.parametrize("relation", list(CODE))
@pytest.mark.parametrize("layout", list(LAYOUTS))
@pytest.mark.parametrize("command", ["check", "verify", "run", "server"])
def test_a_module_is_one_path_and_one_file(
    command: str, layout: str, relation: str, q_first: bool,
    tmp_path: pathlib.Path,
) -> None:
    entry, main = build(tmp_path, layout, relation, q_first)
    code = CODE[relation]
    if command == "run":
        result = pipeline.cli("run", entry)
        if code is None:
            assert (result.returncode, result.stdout.strip()) == (0, "11"), result
        else:
            assert result.returncode != 0
            assert f"[{code}]" in result.stderr, result.stderr
        return
    if command == "server":
        a = analyze(VerificationSession(), entry.as_uri(), main)
        got = [d.code for d in to_lsp_diagnostics(a) if d.code in ("E014", "E015")]
        assert got == ([code] if code else []), got
        return
    diags = check_json(entry, command)
    got = [d for d in diags if d["error_code"] in ("E014", "E015")]
    if code is None:
        assert diags == [], diags
        return
    # One refusal, the same code in both orders.
    assert [d["error_code"] for d in got] == [code], diags
    text = got[0]["description"]
    p_rel, q_rel = LAYOUTS[layout]
    # Both importers are named, whichever was resolved first.
    assert (p_rel or "main.vera") in text and q_rel in text, text
    q_lib = (pathlib.PurePosixPath(q_rel).parent / "lib.vera").as_posix()
    if relation == "one_path_two_files":
        p_lib = (pathlib.PurePosixPath(p_rel).parent / "lib.vera").as_posix() if p_rel else "lib.vera"
        assert f"'{p_lib}'" in text and f"'{q_lib}'" in text, text
    else:
        assert f"'{q_lib}'" in text, text
        assert "'lib'" in text and f"'{module_path(q_lib)}'" in text, text


# --- the reported instance and the pins (every PR runs these) ----------

def _issue_tree(tmp: pathlib.Path, a_mid_first: bool) -> pathlib.Path:
    """The issue's tree: `lib.vera` (1), `a/lib.vera` (2), `a/mid.vera`
    importing `lib`, and `main.vera` importing `a.mid` and `lib`."""
    write(tmp, "lib.vera", "module lib;\n\n" + fn("word", "1"))
    write(tmp, "a/lib.vera", "module lib;\n\n" + fn("word", "2"))
    write(tmp, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "word(())"))
    lines = ["import a.mid(w2);", "import lib(word);"]
    if not a_mid_first:
        lines.reverse()
    return write(tmp, "main.vera", "\n".join(lines) + "\n\n" + main_fn(["word(())", "w2(())"]))


def test_repro_1904_one_path_two_files_is_refused_in_either_order(
    tmp_path: pathlib.Path,
) -> None:
    """`vera run` printed `22` with `a.mid` first and `11` with `lib`
    first; each is now E014."""
    for a_mid_first in (True, False):
        root = tmp_path / str(a_mid_first)
        result = pipeline.cli("run", _issue_tree(root, a_mid_first))
        assert result.returncode != 0 and "[E014]" in result.stderr, result


def test_repro_1904_one_file_two_paths_is_refused(tmp_path: pathlib.Path) -> None:
    """`a/lib.vera` imported as `a.lib` and as `lib` was compiled twice."""
    write(tmp_path, "a/lib.vera", "module a.lib;\n\n" + fn("word", "2"))
    write(tmp_path, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.lib(word);\nimport a.mid(w2);\n\n"
                  + main_fn(["word(())", "w2(())"]))
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E015"]
    assert d["description"] == (
        "'a/lib.vera' is imported by two paths: as 'lib' in 'a/mid.vera', "
        "and as 'a.lib' in 'main.vera'.")


def test_repro_1904_an_unreadable_module_is_reported_once(
    tmp_path: pathlib.Path,
) -> None:
    """The issue's second line: one path, two importers, a file that does
    not decode; E024 was reported once per importer."""
    write(tmp_path, "lib.vera", ("module lib;\n\n" + fn("word", "1")).encode() + b"\xe9")
    write(tmp_path, "mid.vera", "module mid;\n\nimport lib(word);\n\n" + fn("w2", "1"))
    entry = write(tmp_path, "main.vera", "import mid(w2);\nimport lib(word);\n\n"
                  + main_fn(["w2(())"]))
    assert [d["error_code"] for d in check_json(entry)] == ["E024"]


def test_an_unreadable_file_under_two_paths_is_e024_once_and_e015(
    tmp_path: pathlib.Path,
) -> None:
    write(tmp_path, "a/lib.vera", ("module a.lib;\n\n" + fn("word", "2")).encode() + b"\xe9")
    write(tmp_path, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "1"))
    entry = write(tmp_path, "main.vera", "import a.lib(word);\nimport a.mid(w2);\n\n"
                  + main_fn(["w2(())"]))
    assert sorted(d["error_code"] for d in check_json(entry)) == ["E015", "E024"]


def test_a_cycle_through_two_spellings_is_e011_at_the_first_reentry(
    tmp_path: pathlib.Path,
) -> None:
    """`a/lib.vera` -> `mid` -> `lib` (itself, by another path): E011 at
    `a/mid.vera`'s import, where the file is re-entered, before it is read
    a second time."""
    write(tmp_path, "a/lib.vera", "module a.lib;\n\nimport mid(w2);\n\n" + fn("word", "1"))
    write(tmp_path, "a/mid.vera", "module mid;\n\nimport lib(word);\n\n" + fn("w2", "1"))
    entry = write(tmp_path, "main.vera", "import a.lib(word);\n\n" + main_fn(["word(())"]))
    (d,) = check_json(entry)
    assert d["error_code"] == "E011"
    assert pathlib.Path(d["location"]["file"]).parts[-2:] == ("a", "mid.vera")


def test_e012_and_e013_stay_one_per_failing_import(tmp_path: pathlib.Path) -> None:
    write(tmp_path, "lib.vera", "module lib;\n\npublic fn word(@Unit -> @Int\n")
    write(tmp_path, "mid.vera", "module mid;\n\nimport lib(word);\nimport nosuch;\n\n"
          + fn("w2", "1"))
    entry = write(tmp_path, "main.vera", "import mid(w2);\nimport lib(word);\nimport nosuch;\n\n"
                  + main_fn(["w2(())"]))
    got = sorted((d["error_code"], pathlib.Path(d["location"]["file"]).name)
                 for d in check_json(entry))
    assert got == [("E012", "main.vera"), ("E012", "mid.vera"),
                   ("E013", "main.vera"), ("E013", "mid.vera")]


def _server_lines(entry: pathlib.Path, code: str) -> list[int]:
    a = analyze(VerificationSession(), entry.as_uri(), entry.read_text(encoding="utf-8"))
    return [d.range.start.line for d in to_lsp_diagnostics(a) if d.code == code]


def test_a_refusal_in_the_document_stands_at_its_import(tmp_path: pathlib.Path) -> None:
    """`main.vera` meets the conflict (its import of `lib` is the second):
    `vera check` locates it at that import, and the server publishes it
    there."""
    entry = _issue_tree(tmp_path, a_mid_first=True)
    (d,) = check_json(entry)
    assert (pathlib.Path(d["location"]["file"]).name, d["location"]["line"]) == ("main.vera", 2)
    assert _server_lines(entry, "E014") == [1]


def test_a_refusal_in_a_module_stands_at_its_import_there(tmp_path: pathlib.Path) -> None:
    """`a/mid.vera` meets the conflict: `vera check` locates it at
    `a/mid.vera`'s import, as it locates that module's E012, and the server
    publishes it on the document's import of `a.mid` (the #1903 rule)."""
    entry = _issue_tree(tmp_path, a_mid_first=False)
    (d,) = check_json(entry)
    assert pathlib.Path(d["location"]["file"]).parts[-2:] == ("a", "mid.vera")
    assert d["location"]["line"] == 3
    assert _server_lines(entry, "E014") == [1]


# --- what one file is ---------------------------------------------------

def _two_names_one_file(tmp: pathlib.Path, link) -> pathlib.Path | None:
    """`shared/lib.vera` and, made by *link*, `a/lib.vera` naming the same
    file; `a/mid.vera` imports `lib` and `main.vera` imports `shared.lib`."""
    target = write(tmp, "shared/lib.vera", "module lib;\n\n" + fn("word", "2"))
    (tmp / "a").mkdir()
    try:
        link(target, tmp / "a" / "lib.vera")
    except (OSError, NotImplementedError):
        return None
    write(tmp, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "word(())"))
    return write(tmp, "main.vera", "import shared.lib(word);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "w2(())"]))


def test_a_symbolic_link_is_the_file_it_points_at(tmp_path: pathlib.Path) -> None:
    entry = _two_names_one_file(tmp_path, lambda t, n: os.symlink(t, n))
    if entry is None:
        pytest.skip("this platform or account cannot make a symbolic link")
    assert [d["error_code"] for d in check_json(entry)
            if d["error_code"].startswith("E01")] == ["E015"]


def test_two_hard_links_are_one_file(tmp_path: pathlib.Path) -> None:
    """Two names that resolve to two strings and are one file: the
    filesystem's identity decides, not the names."""
    entry = _two_names_one_file(tmp_path, lambda t, n: os.link(t, n))
    if entry is None:
        pytest.skip("this filesystem cannot make a hard link")
    assert [d["error_code"] for d in check_json(entry)
            if d["error_code"].startswith("E01")] == ["E015"]


def _case_insensitive(tmp: pathlib.Path) -> bool:
    probe = write(tmp, "probe_case.txt", "x")
    return (tmp / "PROBE_CASE.txt").exists() and probe.exists()


def test_two_spellings_that_differ_in_case_are_one_file_where_case_is_ignored(
    tmp_path: pathlib.Path,
) -> None:
    """A path part may hold capitals after its first letter, so `liB` and
    `lib` are two paths; on a filesystem that ignores case they reach one
    `lib.vera`, which is E015.  Where case is kept they are two lookups, and
    `liB` finds no file (E012)."""
    write(tmp_path, "lib.vera", "module lib;\n\n" + fn("word", "1"))
    write(tmp_path, "mid.vera", "module mid;\n\nimport liB(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import lib(word);\nimport mid(w2);\n\n"
                  + main_fn(["word(())", "w2(())"]))
    codes = [d["error_code"] for d in check_json(entry) if d["error_code"].startswith("E01")]
    if not _case_insensitive(tmp_path):
        assert codes == ["E012"]
        pytest.skip("this filesystem keeps case: two spellings are two lookups")
    assert codes == ["E015"]


# --- the fixes, applied as written --------------------------------------

_TICKS = re.compile(r"`([^`]+)`")


def _apply_import_edit(diag: dict, root: pathlib.Path) -> None:
    """Apply a fix of the form "write `import X` in FILE in place of
    `import Y`" (FILE the diagnostic's own file when the fix says "here")."""
    fix = diag["fix"]
    m = re.search(r"write `import ([^`]+)` (?:here|in '([^']+)') in place of `import ([^`]+)`", fix)
    assert m, fix
    new, where, old = m.group(1), m.group(2), m.group(3)
    target = (root / where) if where else pathlib.Path(diag["location"]["file"])
    text = target.read_text(encoding="utf-8")
    assert f"import {old}(" in text, (target, old)
    target.write_text(text.replace(f"import {old}(", f"import {new}(", 1), encoding="utf-8")


def test_e014s_fix_applied_clears_it(tmp_path: pathlib.Path) -> None:
    """Rename the file the diagnostic's import found, as the fix names it,
    and write the import it gives in place of the old one."""
    entry = _issue_tree(tmp_path, a_mid_first=True)
    (d,) = check_json(entry)
    ticks = _TICKS.findall(d["fix"])
    old_file, new_file, new_import, old_import = ticks[:4]
    (tmp_path / old_file).rename(tmp_path / new_file)
    here = pathlib.Path(d["location"]["file"])
    text = here.read_text(encoding="utf-8")
    old_path = old_import.removeprefix("import ")
    assert f"import {old_path}(" in text
    here.write_text(text.replace(f"import {old_path}(",
                                 f"{new_import}(", 1), encoding="utf-8")
    assert check_json(entry) == []
    assert pipeline.cli("run", entry).stdout.strip() == "12"


def test_e015s_fix_uses_the_path_that_reaches_it_from_both(tmp_path: pathlib.Path) -> None:
    """`a/mid.vera` imports `a/lib.vera` as `lib`; `main.vera` as `a.lib`,
    which also reaches it from `a/mid.vera` (through the root): the fix
    writes `import a.lib` in `a/mid.vera`, and the program then checks and
    runs."""
    write(tmp_path, "a/lib.vera", "module a.lib;\n\n" + fn("word", "2"))
    write(tmp_path, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.lib(word);\nimport a.mid(w2);\n\n"
                  + main_fn(["word(())", "w2(())"]))
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E015"]
    assert "write `import a.lib` here in place of `import lib`" in d["fix"]
    _apply_import_edit(d, tmp_path)
    assert check_json(entry) == []
    assert pipeline.cli("run", entry).stdout.strip() == "22"


def test_e015s_fix_changes_the_other_importer_when_only_that_works(
    tmp_path: pathlib.Path,
) -> None:
    """The other order: `a/mid.vera` binds the file as `lib` first, and
    `main.vera`'s `a.lib` meets the conflict.  `lib` does not reach the
    file from `main.vera`, but `a.lib` reaches it from `a/mid.vera`, so the
    fix rewrites `a/mid.vera`'s import."""
    write(tmp_path, "a/lib.vera", "module a.lib;\n\n" + fn("word", "2"))
    write(tmp_path, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.mid(w2);\nimport a.lib(word);\n\n"
                  + main_fn(["word(())", "w2(())"]))
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E015"]
    assert pathlib.Path(d["location"]["file"]).name == "main.vera"
    assert "write `import a.lib` in 'a/mid.vera' in place of `import lib`" in d["fix"]
    _apply_import_edit(d, tmp_path)
    assert check_json(entry) == []


def _linked_pair(tmp: pathlib.Path, shadow: bool) -> pathlib.Path | None:
    """`x/p.vera` imports `x/lib.vera` as `lib`; `y/q.vera` imports `z`,
    `y/z.vera`, a hard link to the same file.  Neither path reaches the file
    from the other importer.  With *shadow*, `x/y/z.vera`, another file,
    keeps the root path `y.z` from reaching it from `x/p.vera`."""
    target = write(tmp, "x/lib.vera", "module lib;\n\n" + fn("word", "2"))
    (tmp / "y").mkdir()
    try:
        os.link(target, tmp / "y" / "z.vera")
    except (OSError, NotImplementedError):
        return None
    if shadow:
        write(tmp, "x/y/z.vera", "module z;\n\n" + fn("word", "9"))
    write(tmp, "x/p.vera", "module x.p;\n\nimport lib(word);\n\n" + fn("wp", "word(())"))
    write(tmp, "y/q.vera", "module y.q;\n\nimport z(word);\n\n" + fn("wq", "word(())"))
    return write(tmp, "main.vera", "import x.p(wp);\nimport y.q(wq);\n\n"
                 + main_fn(["wp(())", "wq(())"]))


def test_e015s_fix_uses_the_root_path_when_it_reaches_from_both(
    tmp_path: pathlib.Path,
) -> None:
    """Neither importer's path reaches the file from the other, but its
    path from the project root, `y.z`, reaches it from both: the fix writes
    that import in both files, and the program then checks."""
    entry = _linked_pair(tmp_path, shadow=False)
    if entry is None:
        pytest.skip("this filesystem cannot make a hard link")
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E015"]
    m = re.search(r"write `import ([^`]+)` here in place of `import ([^`]+)` "
                  r"and in '([^']+)' in place of `import ([^`]+)`", d["fix"])
    assert m, d["fix"]
    new, here_old, other, other_old = m.groups()
    assert new == "y.z"
    for target, old in ((pathlib.Path(d["location"]["file"]), here_old),
                        (tmp_path / other, other_old)):
        text = target.read_text(encoding="utf-8")
        target.write_text(text.replace(f"import {old}(", f"import {new}(", 1),
                          encoding="utf-8")
    assert check_json(entry) == []


def test_e015s_fix_says_when_no_path_reaches_it_from_both(tmp_path: pathlib.Path) -> None:
    """With the root path shadowed too, no path reaches the file from both
    importers, and the fix says so and offers no import to write."""
    entry = _linked_pair(tmp_path, shadow=True)
    if entry is None:
        pytest.skip("this filesystem cannot make a hard link")
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E015"]
    assert "reaches it from both files by the lookup of spec section 8.6.1" in d["fix"]
    assert "`import" not in d["fix"], d["fix"]


def test_e014s_new_path_reaches_the_renamed_file_from_its_importer(
    tmp_path: pathlib.Path,
) -> None:
    """`x/q.vera`'s `lib` falls through to the root `lib.vera`, and
    `x/lib2.vera`, another module, sits beside `x/q.vera`.  The fix renames
    the root file to a path whose lookup from `x/q.vera` finds the renamed
    file, not that neighbour: applied, the program checks and `x/q.vera`
    reads the module it imported."""
    write(tmp_path, "lib.vera", "module lib;\n\n" + fn("word", "1"))
    write(tmp_path, "y/lib.vera", "module lib;\n\n" + fn("word", "2"))
    write(tmp_path, "x/lib2.vera", "module lib2;\n\n" + fn("word", "9"))
    write(tmp_path, "y/p.vera", "module y.p;\n\nimport lib(word);\n\n" + fn("wp", "word(())"))
    write(tmp_path, "x/q.vera", "module x.q;\n\nimport lib(word);\n\n" + fn("wq", "word(())"))
    entry = write(tmp_path, "main.vera", "import y.p(wp);\nimport x.q(wq);\n\n"
                  + main_fn(["wp(())", "wq(())"]))
    (d,) = check_json(entry)
    assert d["error_code"] == "E014"
    old_file, new_file, new_import, old_import = _TICKS.findall(d["fix"])[:4]
    assert new_file != "lib2.vera", d["fix"]
    (tmp_path / old_file).rename(tmp_path / new_file)
    here = pathlib.Path(d["location"]["file"])
    text = here.read_text(encoding="utf-8")
    here.write_text(text.replace(old_import + "(",
                                 new_import + "(", 1), encoding="utf-8")
    assert check_json(entry) == []
    assert pipeline.cli("run", entry).stdout.strip() == "21"
