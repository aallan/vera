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

import itertools
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


def refusals(diags: list[dict]) -> list[dict]:
    """The resolver's refusals among *diags*; every other diagnostic is an
    E200, a call into the module a refused import would have bound (a
    refused import binds nothing)."""
    out = [d for d in diags if d["error_code"] in ("E011", "E014", "E015")]
    rest = [d["error_code"] for d in diags if d not in out]
    assert set(rest) <= {"E200", "E230"}, diags
    return out


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


def test_repro_1904_two_conflicts_are_refused_in_every_order(
    tmp_path: pathlib.Path,
) -> None:
    """One program holding both relations over one file: `x/b1.vera`
    imports `lib` (finding `x/lib.vera`), `y/b2.vera` imports `lib` (finding
    `y/lib.vera`) and `b3.vera` imports `y.lib` (finding `y/lib.vera`).  In
    each of the six orders the document can import them, the program is
    refused, and each diagnostic is E014 at an importer of `lib`, E015 at an
    importer of `y/lib.vera`, or a consequence of a refused import (E200 for
    the name it would have supplied).  Which of the two codes are reported
    follows the order (a refused import binds nothing and is not read), so
    the codes are not compared across orders."""
    branches = {"x.b1": ("x/b1.vera", "lib", "f1"),
                "y.b2": ("y/b2.vera", "lib", "f2"),
                "b3": ("b3.vera", "y.lib", "f3")}
    importers = {"E014": {"b1.vera", "b2.vera"}, "E015": {"b2.vera", "b3.vera"}}
    for n, order in enumerate(itertools.permutations(branches)):
        root = tmp_path / str(n)
        write(root, "x/lib.vera", fn("word", "1"))
        write(root, "y/lib.vera", fn("word", "2"))
        for rel, imp, name in branches.values():
            write(root, rel, f"import {imp}(word);\n\n" + fn(name, "word(())"))
        lines = [f"import {m}({branches[m][2]});" for m in order]
        entry = write(root, "main.vera", "\n".join(lines) + "\n\n"
                      + main_fn([f"{branches[m][2]}(())" for m in order]))
        diags = check_json(entry)
        refusals = [d for d in diags if d["error_code"] in importers]
        assert refusals, (order, diags)
        for d in diags:
            name = pathlib.Path(d["location"]["file"]).name
            assert d["error_code"] in ("E014", "E015", "E200"), (order, d)
            if d["error_code"] in importers:
                assert name in importers[d["error_code"]], (order, d)
        result = pipeline.cli("run", entry)
        assert result.returncode != 0, (order, result)


def test_repro_1904_an_import_that_breaks_both_halves_is_e014(
    tmp_path: pathlib.Path,
) -> None:
    """`main.vera` binds `lib` to `lib.vera` and `a.lib` to `a/lib.vera`;
    `a/mid.vera`'s `lib` finds `a/lib.vera`, which breaks both halves at one
    import: its path names another file, and its file has another path.  The
    path is tested first, so the import is one E014, and no E015."""
    write(tmp_path, "lib.vera", fn("word", "1"))
    write(tmp_path, "a/lib.vera", fn("wa", "2"))
    write(tmp_path, "a/mid.vera", "import lib(wa);\n\n" + fn("w2", "wa(())"))
    entry = write(tmp_path, "main.vera",
                  "import lib(word);\nimport a.lib(wa);\nimport a.mid(w2);\n\n"
                  + main_fn(["word(())", "wa(())", "w2(())"]))
    got = [(d["error_code"], pathlib.Path(d["location"]["file"]).parts[-2:])
           for d in check_json(entry) if d["error_code"].startswith("E01")]
    assert got == [("E014", ("a", "mid.vera"))], got


def test_an_import_refused_by_e015_does_not_read_its_file_again(
    tmp_path: pathlib.Path,
) -> None:
    """`a/lib.vera` does not parse: `main.vera`'s `a.lib` reads it (E013),
    and `a/mid.vera`'s `lib`, the same file by another path, is E015 and
    stops there, so the file is not read, and its E013 not reported, a
    second time."""
    write(tmp_path, "a/lib.vera", "public fn word(@Unit -> @Int\n")
    write(tmp_path, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "1"))
    entry = write(tmp_path, "main.vera", "import a.lib(word);\nimport a.mid(w2);\n\n"
                  + main_fn(["w2(())"]))
    got = [(d["error_code"], pathlib.Path(d["location"]["file"]).name)
           for d in check_json(entry)]
    assert got == [("E013", "main.vera"), ("E015", "mid.vera")], got


def test_a_refusal_names_the_import_that_bound_the_path_first(
    tmp_path: pathlib.Path,
) -> None:
    """A module that does not parse is not cached, so a second import of it
    by the same path reads it again; the binding keeps the first importer,
    and a later conflict names that one."""
    one = tmp_path / "e014"
    write(one, "lib.vera", "public fn word(@Unit -> @Int\n")
    write(one, "m.vera", "import lib(word);\n\n" + fn("wm", "1"))
    write(one, "a/lib.vera", fn("word", "2"))
    write(one, "a/q.vera", "import lib(word);\n\n" + fn("wq", "word(())"))
    entry = write(one, "main.vera", "import lib(word);\nimport m(wm);\nimport a.q(wq);\n\n"
                  + main_fn(["wm(())", "wq(())"]))
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E014"]
    assert d["description"].endswith(
        "and 'main.vera' imports it as 'lib.vera'."), d["description"]
    two = tmp_path / "e015"
    write(two, "a/lib.vera", "public fn word(@Unit -> @Int\n")
    write(two, "m.vera", "import a.lib(word);\n\n" + fn("wm", "1"))
    write(two, "a/q.vera", "import lib(word);\n\n" + fn("wq", "1"))
    entry = write(two, "main.vera", "import a.lib(word);\nimport m(wm);\nimport a.q(wq);\n\n"
                  + main_fn(["wm(())", "wq(())"]))
    (d,) = [d for d in check_json(entry) if d["error_code"] == "E015"]
    assert d["description"].endswith(
        "and as 'a.lib' in 'main.vera'."), d["description"]


def test_two_files_on_two_devices_with_one_file_number_are_two_files(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A file's identity is its device and its file number: two files on
    two volumes may share a file number.  A machine whose temporary
    directory is one volume cannot make that pair, so `os.stat` is made to
    report `other.vera` with `lib.vera`'s file number on another device; the
    two are two modules, and the program checks."""
    lib = write(tmp_path, "lib.vera", fn("word", "1"))
    other = write(tmp_path, "other.vera", fn("wo", "2"))
    entry = write(tmp_path, "main.vera", "import lib(word);\nimport other(wo);\n\n"
                  + main_fn(["word(())", "wo(())"]))
    real_stat = os.stat
    lib_st = real_stat(lib)
    other_name = other.resolve()

    def fake_stat(path, *args, **kwargs):
        st = real_stat(path, *args, **kwargs)
        if pathlib.Path(path) == other_name:
            fields = list(st)
            fields[1], fields[2] = lib_st.st_ino, lib_st.st_dev + 1
            return os.stat_result(fields)
        return st

    monkeypatch.setattr(os, "stat", fake_stat)
    assert check_json(entry) == []


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
    (d,) = refusals(check_json(entry))
    assert (pathlib.Path(d["location"]["file"]).name, d["location"]["line"]) == ("main.vera", 2)
    assert _server_lines(entry, "E014") == [1]


def test_a_refusal_in_a_module_stands_at_its_import_there(tmp_path: pathlib.Path) -> None:
    """`a/mid.vera` meets the conflict: `vera check` locates it at
    `a/mid.vera`'s import, as it locates that module's E012, and the server
    publishes it on the document's import of `a.mid` (the #1903 rule)."""
    entry = _issue_tree(tmp_path, a_mid_first=False)
    (d,) = refusals(check_json(entry))
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


# --- one file under two names in two directories ------------------------

def _linked_pair(tmp: pathlib.Path, shadow: bool,
                 q_first: bool = False) -> pathlib.Path | None:
    """`x/p.vera` imports `x/lib.vera` as `lib`; `y/q.vera` imports `z`,
    `y/z.vera`, a hard link to the same file.  Neither path reaches the file
    from the other importer.  With *shadow*, `x/y/z.vera`, another file,
    keeps the root path `y.z` from reaching it from `x/p.vera`.  With
    *q_first*, the document imports `y.q` first, so `x/p.vera` meets the
    conflict."""
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
    lines = ["import x.p(wp);", "import y.q(wq);"]
    if q_first:
        lines.reverse()
    return write(tmp, "main.vera", "\n".join(lines) + "\n\n"
                 + main_fn(["wp(())", "wq(())"]))


def _one_file_two_directories(tmp: pathlib.Path, link, x_first: bool) -> pathlib.Path | None:
    """`x/mid.vera` and `y/mid.vera` each import `lib`; `y/lib.vera` is
    made by *link* from `x/lib.vera`, which imports `dep`; only
    `x/dep.vera` exists.  At ba9dabf8, with a hard link, `x` first ran
    (`44`) and `y` first was `E012`: the first import to reach the file
    decided the directory its `dep` was looked up from."""
    target = write(tmp, "x/lib.vera", "import dep(d);\n\n" + fn("word", "d(())"))
    (tmp / "y").mkdir()
    try:
        link(target, tmp / "y" / "lib.vera")
    except (OSError, NotImplementedError):
        return None
    write(tmp, "x/dep.vera", fn("d", "4"))
    write(tmp, "x/mid.vera", "import lib(word);\n\n" + fn("wx", "word(())"))
    write(tmp, "y/mid.vera", "import lib(word);\n\n" + fn("wy", "word(())"))
    lines = ["import x.mid(wx);", "import y.mid(wy);"]
    if not x_first:
        lines.reverse()
    return write(tmp, "main.vera", "\n".join(lines) + "\n\n" + main_fn(["wx(())", "wy(())"]))


@pytest.mark.parametrize("x_first", [True, False], ids=["x_first", "y_first"])
def test_repro_1904_one_file_in_two_directories_is_refused_in_either_order(
    tmp_path: pathlib.Path, x_first: bool,
) -> None:
    """Two hard links in two directories are one file with two directories:
    E015 at the import that reaches it through the second, in either
    order, naming both names and both importers.  (With `y` first, the
    file's `dep` is looked up from `y/`, and its E012 stands too.)"""
    entry = _one_file_two_directories(tmp_path, os.link, x_first)
    if entry is None:
        pytest.skip("this filesystem cannot make a hard link")
    diags = check_json(entry)
    found = [d for d in diags if d["error_code"] == "E015"]
    assert len(found) == 1, diags
    (d,) = found
    first, second = ("x", "y") if x_first else ("y", "x")
    assert pathlib.Path(d["location"]["file"]).parent.name == second, d
    for name in (f"{first}/lib.vera", f"{second}/lib.vera",
                 f"{first}/mid.vera", f"{second}/mid.vera"):
        assert f"'{name}'" in d["description"] and name in d["fix"], (name, d)
    assert "two directories" in d["description"], d
    assert {x["error_code"] for x in diags} <= {"E015", "E012", "E200"}, diags
    assert pipeline.cli("run", entry).returncode != 0


@pytest.mark.parametrize("x_first", [True, False], ids=["x_first", "y_first"])
def test_a_symbolic_link_has_its_targets_one_directory(
    tmp_path: pathlib.Path, x_first: bool,
) -> None:
    """The control: `y/lib.vera` a symbolic link to `x/lib.vera` is one
    entry, the target's, so both imports reach the file in `x/`, its `dep`
    is looked up from there in either order, and the program runs."""
    entry = _one_file_two_directories(tmp_path, os.symlink, x_first)
    if entry is None:
        pytest.skip("this platform or account cannot make a symbolic link")
    assert check_json(entry) == []
    assert pipeline.cli("run", entry).stdout.strip() == "44"


# --- the project root as the command line names it ---------------------

def test_a_document_named_relative_to_the_working_directory(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The project root is the entry's directory as the command line names
    it, here `.`; the diagnostics and their fixes name files from it, as
    for an absolute entry."""
    one = tmp_path / "one"
    _issue_tree(one, a_mid_first=True)
    two = tmp_path / "two"
    _shape_e015_here(two)
    for root in (one, two):
        absolute = check_json(root / "main.vera")
        monkeypatch.chdir(root)
        relative = check_json(pathlib.Path("main.vera"))
        keep = ("error_code", "description", "fix")
        assert ([{k: d[k] for k in keep} for d in relative]
                == [{k: d[k] for k in keep} for d in absolute]), relative


# --- review round 1 -------------------------------------------------------

def _stat_fails_for(monkeypatch: pytest.MonkeyPatch, name: str) -> None:
    """`os.stat` of a file named *name* raises, as for a file removed or
    made unreadable after the lookup found it, when `file_identity` asks;
    the lookup's own `is_file` still sees the file."""
    import sys

    real_stat = os.stat

    def stat(path, *args, **kwargs):
        if (pathlib.Path(path).name == name
                and sys._getframe(1).f_code.co_name == "file_identity"):
            raise FileNotFoundError(2, "No such file or directory", str(path))
        return real_stat(path, *args, **kwargs)

    monkeypatch.setattr(os, "stat", stat)


def test_a_file_that_cannot_be_identified_is_e013_at_its_import(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The lookup finds `lib.vera`, and the file is gone before its identity
    is read: the import cannot read it, which is E013 at the import, once,
    and the resolver does not raise."""
    write(tmp_path, "lib.vera", fn("word", "1"))
    entry = write(tmp_path, "main.vera", "import lib(word);\n\n" + main_fn(["word(())"]))
    _stat_fails_for(monkeypatch, "lib.vera")
    got = [(d["error_code"], pathlib.Path(d["location"]["file"]).name, d["location"]["line"])
           for d in check_json(entry) if d["error_code"].startswith("E01")]
    assert got == [("E013", "main.vera", 1)], got


def _refused_import_tree(tmp: pathlib.Path, in_module: bool) -> pathlib.Path:
    """One path, two files, and a call into the module the REFUSED import
    would have bound, to a name only the other file declares.  With
    *in_module*, `a/mid.vera` holds the refused import and the call;
    else the document does."""
    if in_module:
        write(tmp, "lib.vera", fn("word", "1") + "\n" + fn("only_root", "5"))
        write(tmp, "a/lib.vera", fn("word", "2"))
        write(tmp, "a/mid.vera", "import lib;\n\n" + fn("w2", "word(())"))
        return write(tmp, "main.vera", "import lib(word);\nimport a.mid(w2);\n\n"
                     + main_fn(["word(())", "w2(())"]))
    write(tmp, "lib.vera", fn("word", "1"))
    write(tmp, "a/lib.vera", fn("word", "2") + "\n" + fn("only_a", "5"))
    write(tmp, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(tmp, "main.vera", "import a.mid(w2);\nimport lib;\n\n"
                 + main_fn(["word(())", "w2(())"]))


@pytest.mark.parametrize("in_module", [False, True], ids=["document", "module"])
def test_repro_1904_a_refused_import_binds_nothing(
    tmp_path: pathlib.Path, in_module: bool,
) -> None:
    """The refused import's own module would have supplied `word`; the
    module another importer bound its path to also declares `word`, and
    `only_a` / `only_root` beside it.  The refused import binds neither: its
    importer's call of `word` is unresolved (E200), where the other file's
    `word` was taken silently."""
    entry = _refused_import_tree(tmp_path, in_module)
    diags = check_json(entry)
    where = ("a", "mid.vera") if in_module else ("main.vera",)
    got = sorted((d["error_code"], pathlib.Path(d["location"]["file"]).parts[-len(where):])
                 for d in diags)
    assert got == [("E014", where), ("E200", where)], diags


def test_a_refused_import_carries_no_modules_diagnostics_in_the_server(
    tmp_path: pathlib.Path,
) -> None:
    """The issue's tree, `a.mid` first, `a/lib.vera` holding a type error:
    the document's own `import lib` is refused, so the server publishes the
    module's error on the import that reaches it, `import a.mid` (line 0),
    and not on the refused one."""
    write(tmp_path, "lib.vera", fn("word", "1"))
    write(tmp_path, "a/lib.vera", fn("word", "true"))
    write(tmp_path, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.mid(w2);\nimport lib;\n\n"
                  + main_fn(["w2(())"]))
    a = analyze(VerificationSession(), entry.as_uri(), entry.read_text(encoding="utf-8"))
    lines = {d.code: d.range.start.line for d in to_lsp_diagnostics(a)}
    assert lines.get("E014") == 1, lines
    module_errors = [d for d in to_lsp_diagnostics(a) if d.code not in ("E014", "E200")]
    assert module_errors and all(d.range.start.line == 0 for d in module_errors), lines


@pytest.mark.parametrize("link_first", [False, True], ids=["link_meets", "link_bound"])
def test_e014_names_the_link_the_lookup_found(
    tmp_path: pathlib.Path, link_first: bool,
) -> None:
    """`a/lib.vera` is a symbolic link to `shared/lib.vera`: E014 names the
    link, the name `a/mid.vera`'s lookup found, on either side of the
    conflict, and its fix names the same two files and proposes no name."""
    target = write(tmp_path, "shared/lib.vera", fn("word", "2"))
    (tmp_path / "a").mkdir()
    try:
        os.symlink(target, tmp_path / "a" / "lib.vera")
    except (OSError, NotImplementedError):
        pytest.skip("this platform or account cannot make a symbolic link")
    write(tmp_path, "lib.vera", fn("word", "1"))
    write(tmp_path, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    lines = ["import lib(word);", "import a.mid(w2);"]
    if link_first:
        lines.reverse()
    entry = write(tmp_path, "main.vera", "\n".join(lines) + "\n\n"
                  + main_fn(["word(())", "w2(())"]))
    (d,) = refusals(check_json(entry))
    assert "as 'a/lib.vera'" in d["description"] and "shared" not in d["description"], d
    assert "`a/lib.vera`" in d["fix"] and "shared" not in d["fix"], d
    assert _proposes_nothing(d), d["fix"]


def test_a_refused_import_is_not_qualified_callable(tmp_path: pathlib.Path) -> None:
    """The document's refused `import lib` does not make `lib::` callable,
    though the path `lib` names another file's module in the program: the
    qualified call into it is E230, as for a module the document does not
    import."""
    write(tmp_path, "lib.vera", fn("word", "1"))
    write(tmp_path, "a/lib.vera", fn("word", "2") + "\n" + fn("only_a", "5"))
    write(tmp_path, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.mid(w2);\nimport lib;\n\n"
                  + main_fn(["lib::only_a(())", "w2(())"]))
    got = sorted(d["error_code"] for d in check_json(entry))
    assert got == ["E014", "E230"], got


def test_a_refusal_applies_to_the_document_however_its_name_is_spelled(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Through the library: the resolver is handed `Path("./main.vera")` and
    the checker the string `"./main.vera"`.  They name one file, so the
    document's refused import binds nothing (its call is E200)."""
    from vera.checker import typecheck
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform

    entry = _refused_import_tree(tmp_path, in_module=False)
    monkeypatch.chdir(tmp_path)
    source = entry.read_text(encoding="utf-8")
    program = transform(parse(source, file="./main.vera"))
    resolver = ModuleResolver(_root=pathlib.Path("."))
    resolved = resolver.resolve_imports(program, pathlib.Path("./main.vera"))
    assert [d.error_code for d in resolver.errors] == ["E014"]
    codes = [d.error_code for d in typecheck(program, source, file="./main.vera",
                                              resolved_modules=resolved)]
    assert codes == ["E200"], codes


# --- the rule in prose ---------------------------------------------------
#
# E014's and E015's fix states the rule and what must end up true; it names
# no file to create and no import to write.  Each shape below broke a
# concrete repair in an earlier form of this change; each now gets the
# prose, naming the files its description names.

def _shape_later_binding(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """`main` imports `a.mid`, `lib`, then `b.mid`, which binds `lib2` to
    `b/lib2.vera` after the conflict is met: `lib2` is not free."""
    _issue_tree_files(r)
    write(r, "b/lib2.vera", fn("w3", "3"))
    write(r, "b/mid.vera", "import lib2(w3);\n\n" + fn("wb", "w3(())"))
    return write(r, "main.vera", "import a.mid(w2);\nimport lib(word);\nimport b.mid(wb);\n\n"
                 + main_fn(["word(())", "w2(())", "wb(())"])), "123"


def _issue_tree_files(r: pathlib.Path) -> None:
    write(r, "lib.vera", "module lib;\n\n" + fn("word", "1"))
    write(r, "a/lib.vera", "module lib;\n\n" + fn("word", "2"))
    write(r, "a/mid.vera", "module a.mid;\n\nimport lib(word);\n\n" + fn("w2", "word(())"))


def _shape_issue(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    return _issue_tree(r, a_mid_first=True), "12"


def _shape_own_path(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """The renamed file declares `module lib;` and calls `lib::helper` on
    itself: the repair renames the declaration and the call with it."""
    write(r, "lib.vera", "module lib;\n\n" + fn("helper", "1") + "\n" + fn("word", "lib::helper(())"))
    write(r, "a/lib.vera", "module lib;\n\n" + fn("word", "2"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import a.mid(w2);\nimport lib(word);\n\n"
                 + main_fn(["word(())", "w2(())"])), "12"


def _shape_fallback(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    entry = _issue_tree(r, a_mid_first=True)
    for n in range(2, 100):
        write(r, f"lib{n}.vera", fn("word", "0"))
    return entry, "12"


def _shape_none_free(r: pathlib.Path) -> tuple[pathlib.Path, str | None]:
    entry, _ = _shape_fallback(r)
    write(r, "lib_renamed.vera", fn("word", "77"))
    return entry, None


def _shape_link(r: pathlib.Path, link_first: bool) -> tuple[pathlib.Path, str] | None:
    target = write(r, "shared/lib.vera", fn("word", "2"))
    (r / "a").mkdir(parents=True)
    try:
        os.symlink(target, r / "a" / "lib.vera")
    except (OSError, NotImplementedError):
        return None
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    lines = ["import lib(word);", "import a.mid(w2);"]
    if link_first:
        lines.reverse()
    return write(r, "main.vera", "\n".join(lines) + "\n\n"
                 + main_fn(["word(())", "w2(())"])), "12"


def _shape_hard_link(r: pathlib.Path) -> tuple[pathlib.Path, str] | None:
    entry = _linked_pair(r, shadow=False)
    return None if entry is None else (entry, "22")


def _shape_bound_shared_path(r: pathlib.Path) -> tuple[pathlib.Path, str | None] | None:
    """`c/r.vera` binds `y.z` to `c/y/z.vera` first; then `x/p.vera` and
    `y/q.vera` import one hard-linked file as `lib` and `z`.  `y.z` would
    reach the file from both, but names another file in the program: no
    import repairs it."""
    target = write(r, "x/lib.vera", fn("word", "2"))
    (r / "y").mkdir(parents=True)
    try:
        os.link(target, r / "y" / "z.vera")
    except (OSError, NotImplementedError):
        return None
    write(r, "c/y/z.vera", fn("w7", "7"))
    write(r, "c/r.vera", "import y.z(w7);\n\n" + fn("wr", "w7(())"))
    write(r, "x/p.vera", "import lib(word);\n\n" + fn("wp", "word(())"))
    write(r, "y/q.vera", "import z(word);\n\n" + fn("wq", "word(())"))
    return write(r, "main.vera", "import c.r(wr);\nimport x.p(wp);\nimport y.q(wq);\n\n"
                 + main_fn(["wr(())", "wp(())", "wq(())"])), None


def _shape_e015_here(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import a.lib(word);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "w2(())"])), "22"


def _shape_e015_there(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import a.mid(w2);\nimport a.lib(word);\n\n"
                 + main_fn(["word(())", "w2(())"])), "22"


def _prose(built):
    """An out-of-domain shape: a link is in play, so no repair is composed."""
    return None if built is None else (built[0], None)


def _shape_unedited_fallback(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """Renaming `a/x/lib.vera` would send `a/x/other.vera`'s unedited
    `lib` to the root `lib.vera`, a different module that checks clean:
    the program would print `192` where it means `122`."""
    write(r, "x/lib.vera", fn("word", "1"))
    write(r, "a/x/lib.vera", fn("word", "2"))
    write(r, "lib.vera", fn("word", "9"))
    write(r, "a/mid.vera", "import x.lib(word);\n\n" + fn("w2", "word(())"))
    write(r, "a/x/other.vera", "import lib(word);\n\n" + fn("w3", "word(())"))
    return write(r, "main.vera", "import x.lib(word);\nimport a.x.other(w3);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "w3(())", "w2(())"])), "122"


def _shape_link_nested(r: pathlib.Path) -> tuple[pathlib.Path, str] | None:
    """`a/lib.vera` links to `shared/lib.vera`, whose `import dep` the
    resolver looks up from `shared/` (`shared/dep.vera`), not `a/`."""
    write(r, "shared/lib.vera", "import dep(d);\n\n" + fn("word", "d(())"))
    write(r, "shared/dep.vera", fn("d", "5"))
    write(r, "dep.vera", fn("d", "7"))
    (r / "a").mkdir(parents=True)
    try:
        os.symlink(r / "shared" / "lib.vera", r / "a" / "lib.vera")
    except (OSError, NotImplementedError):
        return None
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import lib(word);\nimport dep(d);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "d(())", "w2(())"])), "175"


def _shape_link_to_renamed(r: pathlib.Path) -> tuple[pathlib.Path, str] | None:
    """The root `alias.vera` links to `a/lib.vera`, the file a rename would
    move: renaming it would leave `main.vera`'s `import alias` dangling."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/lib.vera", fn("wa", "2"))
    try:
        os.symlink(r / "a" / "lib.vera", r / "alias.vera")
    except (OSError, NotImplementedError):
        return None
    write(r, "a/mid.vera", "import lib(wa);\n\n" + fn("w2", "wa(())"))
    return write(r, "main.vera", "import lib(word);\nimport alias(wa);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "wa(())", "w2(())"])), "122"


def _shape_e014_qualified(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """The document calls `lib::word` through the import the rename
    changes: the call is renamed with it."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import a.mid(w2);\nimport lib;\n\n"
                 + main_fn(["lib::word(())", "w2(())"])), "12"


def _shape_e015_qualified(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """`a/mid.vera` calls `lib::word` through the import E015's fix
    rewrites to `a.lib`: the call is rewritten with it."""
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/mid.vera", "import lib;\n\n" + fn("w2", "lib::word(())"))
    return write(r, "main.vera", "import a.lib(word);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "w2(())"])), "22"


def _shape_refused_subtree_conflict(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """The refused `a/lib.vera` imports `n.inner`, whose `util` finds
    `n/util.vera`; `main.vera` imports the root `util.vera`.  Resolution
    never reads `a/lib.vera`, so it reports no conflict on `util`; a rename
    would make it read, and `main.vera`'s clean `import util` would be
    refused.  No rename keeps the guarantee."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/lib.vera", "import n.inner(wi);\n\n" + fn("word", "wi(())"))
    write(r, "n/inner.vera", "import util(u);\n\n" + fn("wi", "u(())"))
    write(r, "n/util.vera", fn("u", "6"))
    write(r, "util.vera", fn("u", "4"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import lib(word);\nimport a.mid(w2);\nimport util(u);\n\n"
                 + main_fn(["word(())", "w2(())", "u(())"])), "164"


def _shape_refused_own_conflict(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """The refused `a/lib.vera` itself imports `dep`, which finds
    `a/dep.vera` beside it where `main.vera`'s finds the root's: renamed and
    read, its import would be refused."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "dep.vera", fn("d", "7"))
    write(r, "a/dep.vera", fn("d", "5"))
    write(r, "a/lib.vera", "import dep(d);\n\n" + fn("word", "d(())"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import lib(word);\nimport dep(d);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "d(())", "w2(())"])), "175"


def _shape_refused_subtree_missing(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """The refused `a/lib.vera` imports `nosuch`, which no file holds:
    renamed and read, that import would be `E012`, which resolution never
    reported."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/lib.vera", "import nosuch;\n\n" + fn("word", "2"))
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import lib(word);\nimport a.mid(w2);\n\n"
                 + main_fn(["word(())", "w2(())"])), "12"


def _shape_linked_importer(r: pathlib.Path) -> tuple[pathlib.Path, str] | None:
    """`b/link.vera` links to `a/other.vera`, whose `lib2` is looked up from
    `a/` (resolution reads a module's imports from the directory of the
    file it resolves to): renaming `a/lib.vera` to `a/lib2.vera` would
    capture it, so the fix takes `lib3`.  The file in play is plain."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "lib2.vera", fn("w8", "8"))
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/other.vera", "import lib2(w8);\n\n" + fn("wx", "w8(())"))
    (r / "b").mkdir(parents=True)
    try:
        os.symlink(r / "a" / "other.vera", r / "b" / "link.vera")
    except (OSError, NotImplementedError):
        return None
    write(r, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    return write(r, "main.vera", "import lib(word);\nimport a.mid(w2);\nimport b.link(wx);\n\n"
                 + main_fn(["word(())", "w2(())", "wx(())"])), "128"


def _shape_refused_in_linked_module(r: pathlib.Path) -> tuple[pathlib.Path, str] | None:
    """`b/link.vera` links to `a/other.vera`, whose `lib` resolution looks
    up from `a/` and finds `a/lib.vera`: E014 there.  The file in play is
    plain, so the rename is offered, and the check reads the new import
    from `a/` too, where the rename puts the file."""
    write(r, "lib.vera", fn("word", "1"))
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/other.vera", "import lib(word);\n\n" + fn("wx", "word(())"))
    (r / "b").mkdir(parents=True)
    try:
        os.symlink(r / "a" / "other.vera", r / "b" / "link.vera")
    except (OSError, NotImplementedError):
        return None
    return write(r, "main.vera", "import lib(word);\nimport b.link(wx);\n\n"
                 + main_fn(["word(())", "wx(())"])), "12"


def _shape_e015_other_qualified(r: pathlib.Path) -> tuple[pathlib.Path, str]:
    """E015's second branch: `a/mid.vera` binds the file as `lib` and calls
    `lib::word`; the fix rewrites that import, and that call, in
    `a/mid.vera`."""
    write(r, "a/lib.vera", fn("word", "2"))
    write(r, "a/mid.vera", "import lib;\n\n" + fn("w2", "lib::word(())"))
    return write(r, "main.vera", "import a.mid(w2);\nimport a.lib(word);\n\n"
                 + main_fn(["word(())", "w2(())"])), "22"


#: In-domain shapes whose every candidate fails the check: the fix is then
#: the prose, and nothing is applied.
SHAPES = {
    "issue": _shape_issue,
    "later_binding": _shape_later_binding,
    "own_path": _shape_own_path,
    "fallback": _shape_fallback,
    "none_free": _shape_none_free,
    "link_meets": lambda r: _prose(_shape_link(r, link_first=False)),
    "link_bound": lambda r: _shape_link(r, link_first=True),
    "hard_link": lambda r: _prose(_shape_hard_link(r)),
    "unedited_fallback": lambda r: _shape_unedited_fallback(r),
    "link_nested_lookup": lambda r: _prose(_shape_link_nested(r)),
    "link_to_renamed": lambda r: _prose(_shape_link_to_renamed(r)),
    "e014_qualified_calls": lambda r: _shape_e014_qualified(r),
    "e015_qualified_calls": lambda r: _shape_e015_qualified(r),
    "bound_shared_path": _shape_bound_shared_path,
    "e015_this_import": _shape_e015_here,
    "e015_other_import": _shape_e015_there,
    "refused_subtree_conflict": _shape_refused_subtree_conflict,
    "refused_own_conflict": _shape_refused_own_conflict,
    "refused_subtree_missing": _shape_refused_subtree_missing,
    "linked_importer": _shape_linked_importer,
    "refused_in_linked_module": _shape_refused_in_linked_module,
    "e015_other_qualified_calls": _shape_e015_other_qualified,
}


def _proposes_nothing(diag: dict) -> bool:
    """The fix names no file to create (no `rename X to Y`) and no
    import to write."""
    return (not re.search(r"rename `[^`]+` to `", diag["fix"])
            and "`import " not in diag["fix"])


@pytest.mark.parametrize("shape", list(SHAPES))
def test_every_shape_gets_the_rule_in_prose(tmp_path: pathlib.Path, shape: str) -> None:
    """Each shape's refusal: its fix leads with its code's rule, names every
    file its description names (the two files, or the file, and the two
    importers), and proposes no new name and no import to write."""
    built = SHAPES[shape](tmp_path)
    if built is None:
        pytest.skip("this platform or account cannot make the link")
    entry, _ = built
    (d,) = refusals(check_json(entry))
    lead = ("Give one of the two modules another path" if d["error_code"] == "E014"
            else "Import `" if "two paths" in d["description"] else "Give the file one directory")
    assert d["fix"].startswith(lead), d["fix"]
    for name in re.findall(r"'([^']+\.vera)'", d["description"]):
        assert name in d["fix"], (name, d["fix"])
    assert _proposes_nothing(d), d["fix"]


def _offers_nothing(diag: dict) -> bool:
    return _proposes_nothing(diag)


def test_a_rename_that_strands_another_import_is_not_offered(tmp_path: pathlib.Path) -> None:
    """`x/q.vera`'s `lib` finds `x/lib.vera`, which `main.vera` also
    imports, as `x.lib`.  Renaming `x/lib.vera` would leave `main.vera`'s
    import finding no file, so no rename is offered."""
    write(tmp_path, "lib.vera", fn("word", "1"))
    write(tmp_path, "x/lib.vera", fn("wx", "2"))
    write(tmp_path, "x/q.vera", "import lib(wx);\n\n" + fn("wq", "wx(())"))
    entry = write(tmp_path, "main.vera", "import lib(word);\nimport x.lib(wx);\nimport x.q(wq);\n\n"
                  + main_fn(["word(())", "wx(())", "wq(())"]))
    (d,) = refusals(check_json(entry))
    assert d["error_code"] == "E014" and _offers_nothing(d), d["fix"]


def test_a_repair_that_leaves_a_third_file_under_the_path_is_not_offered(
    tmp_path: pathlib.Path,
) -> None:
    """Three files under `lib`: renaming one of the two refused ones leaves
    the path naming two files still, so neither E014 offers it."""
    for n, d in enumerate("xyz", start=1):
        write(tmp_path, f"{d}/lib.vera", fn("word", str(n)))
        write(tmp_path, f"{d}/p.vera", "import lib(word);\n\n" + fn(f"w{d}", "word(())"))
    entry = write(tmp_path, "main.vera", "import x.p(wx);\nimport y.p(wy);\nimport z.p(wz);\n\n"
                  + main_fn(["wx(())", "wy(())", "wz(())"]))
    found = refusals(check_json(entry))
    assert [d["error_code"] for d in found] == ["E014", "E014"], found
    assert all(_offers_nothing(d) for d in found), [d["fix"] for d in found]


def test_a_repair_that_leaves_a_third_path_to_the_file_is_not_offered(
    tmp_path: pathlib.Path,
) -> None:
    """`a/lib.vera` imported as `a.lib`, as `lib`, and, through a hard link
    at the root, as `alias`: one import changed leaves the file under two
    paths still, so neither E015 offers it."""
    target = write(tmp_path, "a/lib.vera", fn("word", "2"))
    try:
        os.link(target, tmp_path / "alias.vera")
    except (OSError, NotImplementedError):
        pytest.skip("this filesystem cannot make a hard link")
    write(tmp_path, "a/mid.vera", "import lib(word);\n\n" + fn("w2", "word(())"))
    write(tmp_path, "c/r.vera", "import alias(word);\n\n" + fn("w3", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.lib(word);\nimport a.mid(w2);\nimport c.r(w3);\n\n"
                  + main_fn(["word(())", "w2(())", "w3(())"]))
    found = refusals(check_json(entry))
    assert [d["error_code"] for d in found] == ["E015", "E015"], found
    assert all(_offers_nothing(d) for d in found), [d["fix"] for d in found]


# --- a third path to one file --------------------------------------------

def test_a_repair_that_leaves_a_third_plain_path_to_the_file_is_not_offered(
    tmp_path: pathlib.Path,
) -> None:
    """`a/b/lib.vera` imported as `a.b.lib` (`main.vera`), `lib`
    (`a/b/m.vera`) and `b.lib` (`a/m.vera`), every name a plain file: one
    import changed leaves the file under two paths, so neither E015 offers
    a repair."""
    write(tmp_path, "a/b/lib.vera", fn("word", "2"))
    write(tmp_path, "a/b/m.vera", "import lib(word);\n\n" + fn("w1", "word(())"))
    write(tmp_path, "a/m.vera", "import b.lib(word);\n\n" + fn("w2", "word(())"))
    entry = write(tmp_path, "main.vera", "import a.b.lib(word);\nimport a.b.m(w1);\nimport a.m(w2);\n\n"
                  + main_fn(["word(())", "w1(())", "w2(())"]))
    found = refusals(check_json(entry))
    assert [d["error_code"] for d in found] == ["E015", "E015"], found
    assert all(_offers_nothing(d) for d in found), \
        [d["fix"] for d in found]
