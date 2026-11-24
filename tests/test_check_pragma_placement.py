"""Tests for `scripts/check_pragma_placement.py` (#1838): where mutmut files each
`# pragma: no mutate`, read without the engine.

The shapes below pin the gate's rule; the repository cell holds `vera/` to it;
and where mutmut is installed (the Mutation (diff) lane's self-test step) the
differential holds the rule to mutmut's own `PragmaVisitor`, over the shapes
and over every file of `vera/` that carries a pragma.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = ROOT / "scripts" / "check_pragma_placement.py"


def _load() -> object:
    spec = importlib.util.spec_from_file_location("check_pragma_placement", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_pragma_placement"] = module
    spec.loader.exec_module(module)
    return module


gate = _load()

P = "# pragma: no mutate"

#: Each shape: its source, and for each pragma the line it is written on and
#: the line the engine files it under (None: no visitor reads it).
SHAPES: dict[str, tuple[str, list[tuple[int, int | None]]]] = {
    "one_line_statement": (f"x = f(1)  {P} — r\n", [(1, 1)]),
    "after_a_call_that_spans_lines": (
        f"x = f(\n    1,\n    2)  {P} — r\n", [(3, 1)]),
    "below_a_comment_and_a_blank_line": (
        f"# a note\n\nx = f(\n    1)  {P} — r\n", [(4, 3)]),
    "inside_the_brackets_after_a_comma": (
        f"x = f(\n    1,\n    2,  {P} — r\n)\n", [(3, 3)]),
    "before_a_closing_bracket_on_its_own_line": (
        f"x = f(\n    1,\n    2  {P} — r\n)\n", [(3, 3)]),
    "after_the_colon_of_a_condition_that_spans_lines": (
        f"if (a  {P} — r\n        or b):  {P} — r\n    pass\n", [(1, 1), (2, 1)]),
    "the_same_condition_with_its_bracket_on_a_line_of_its_own": (
        f"if (a  {P} — r\n        or b  {P} — r\n):\n    pass\n", [(1, 1), (2, 2)]),
    "a_one_line_header": (f"if a:  {P} — r\n    pass\n", [(1, 1)]),
    "a_one_line_suite": (f"if a: b = 1  {P} — r\n", [(1, 1)]),
    "a_decorated_def_whose_signature_spans_lines": (
        f"@d\ndef f(\n    a,\n):  {P} — r\n    return a\n", [(4, 2)]),
    "a_match_whose_subject_spans_lines": (
        f"match (\n    a\n):  {P} — r\n    case 1:\n        pass\n    case _:\n        pass\n",
        [(3, 1)]),
    "an_except_whose_types_span_lines": (
        f"try:\n    pass\nexcept (A,\n        B):  {P} — r\n    pass\n", [(4, 3)]),
    "an_else_header":(f"if a:\n    pass\nelse:  {P} — r\n    pass\n", [(3, 3)]),
    "alone_on_its_line_bare": (f"def f():\n    {P} — r\n    return 1\n", [(2, 2)]),
    "alone_start_and_end": (
        f"def f():\n    {P} start — r\n    x = 1\n    {P} end\n    return x\n", [(2, 2), (4, 4)]),
    "a_block_token_inside_brackets": (
        f"x = f(\n    1,  {P} block\n)\n", [(2, None)]),
    "a_block_header": (f"if a:  {P} block\n    x = 1\n    y = 2\n", [(1, 1)]),
    "a_region_alone_inside_brackets": (
        f"x = (\n    {P} start\n    1\n    {P} end\n)\n", [(2, None), (4, None)]),
    "a_bare_pragma_alone_inside_brackets": (f"x = f(\n    {P} — r\n    1,\n)\n", [(2, None)]),
    "on_a_decorators_line": (f"@d  {P} — r\ndef f():\n    pass\n", [(1, None)]),
    "a_block_alone_after_a_decorator": (
        f"@d\n{P} block\ndef f():\n    x = 1\n", [(2, None)]),
    "a_block_alone_between_decorators": (
        f"@d\n{P} block\n@e\ndef f():\n    x = 1\n", [(2, None)]),
    "a_block_alone_above_an_else_at_its_indent": (
        f"if a:\n    x = 1\n{P} block\nelse:\n    x = 2\n", [(3, None)]),
    "a_region_in_a_blocks_footer_above_an_else": (
        f"if a:\n    x = 1\n    {P} start\n    y = 2\n    {P} end\nelse:\n    x = 2\n",
        [(3, 3), (5, 5)]),
    "alone_above_a_decorated_def": (
        f"{P} start\n@d\ndef f():\n    pass\n{P} end\n", [(1, 1), (5, 5)]),
    "a_comment_that_is_no_pragma": ("x = f(\n    1)  # pragma: no cover\n", []),
    "the_words_inside_a_string": (f'x = "{P}"\n', []),
}

#: Shapes the engine reads as written; every other has a misplaced pragma.
WELL_PLACED = {
    "one_line_statement", "inside_the_brackets_after_a_comma",
    "before_a_closing_bracket_on_its_own_line", "the_same_condition_with_its_bracket_on_a_line_of_its_own",
    "a_one_line_header", "a_one_line_suite", "an_else_header", "alone_start_and_end",
    "a_comment_that_is_no_pragma", "the_words_inside_a_string",
    "a_block_header", "a_region_in_a_blocks_footer_above_an_else", "alone_above_a_decorated_def",
}


@pytest.mark.parametrize("name", sorted(SHAPES))
def test_each_shape_is_filed_where_the_engine_files_it(name: str) -> None:
    source, expected = SHAPES[name]
    found = gate.pragmas(source)
    assert [(p.line, p.filed) for p in found] == expected
    assert (not gate.check_source(source)) == (name in WELL_PLACED)


def test_a_bare_pragma_alone_on_its_line_is_refused() -> None:
    """It is filed under its own line, where no node starts."""
    (p,) = gate.pragmas(SHAPES["alone_on_its_line_bare"][0])
    assert p.misplaced and "protects no node" in gate.explain(p)


def test_repro_a_pragma_above_a_clause_after_a_one_line_suite_is_read_by_no_visitor() -> None:
    """A one-line suite has no footer, so libcst gives a comment line below
    it to the next clause's own leading lines, which no visitor scans, at
    any indent; an indented block's footer above the same clause is read."""
    (p,) = gate.pragmas(f"if a: x = 1\n    {P} block\nelse: x = 2\n")
    assert (p.filed, p.how, p.misplaced) == (None, "above a clause", True)
    (q,) = gate.pragmas(f"if a:\n    x = 1\n    {P} block\nelse:\n    x = 2\n")
    assert (q.filed, q.misplaced) == (3, False)


def test_repro_a_comment_line_after_a_backslash_ends_the_statement_it_continues() -> None:
    """The engine files it under the statement's first line, as a trailing
    comment, though nothing but the comment is on its own line."""
    (p,) = gate.pragmas(f"x = 1 \\\n    {P} block\n")
    assert (p.filed, p.how, p.misplaced) == (1, "statement", True)


def test_repro_a_comment_line_below_a_pragma_makes_it_footer() -> None:
    """libcst's footer runs through the last comment line deep enough for
    the block, so an ordinary comment below the pragma decides; without it
    the same pragma is the clause's own leading line."""
    (p,) = gate.pragmas(f"if a:\n    x = 1\n{P} block\n    # a note\nelse:\n    x = 2\n")
    assert (p.filed, p.misplaced) == (3, False)
    (q,) = gate.pragmas(f"if a:\n    x = 1\n{P} block\n# a note\nelse:\n    x = 2\n")
    assert (q.filed, q.misplaced) == (None, True)


def test_repro_the_indented_comment_lines_ending_a_module_are_one_line_at_their_first() -> None:
    """libcst keeps the run as one footer line, the run's last comment at
    the run's first line: the last is filed one line up, the others nowhere."""
    (p,) = gate.pragmas(f"x = 1\n    # a note\n  {P} block\n")
    assert (p.filed, p.misplaced) == (2, True)
    (q,) = gate.pragmas(f"x = 1\n  {P} block\n    # a note\n")
    assert (q.filed, q.misplaced) == (None, True)
    (r,) = gate.pragmas(f"x = 1\n  {P} block\n")
    assert (r.filed, r.misplaced) == (2, False)


def test_the_message_names_the_line_the_engine_files_it_under() -> None:
    (p,) = gate.check_source(SHAPES["after_a_call_that_spans_lines"][0])
    assert "filed under line 1" in gate.explain(p) and "not under line 3" in gate.explain(p)


def test_main_exits_one_on_a_misplaced_pragma_and_names_it(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    bad = tmp_path / "bad.py"
    bad.write_text(SHAPES["after_a_call_that_spans_lines"][0], encoding="utf-8")
    good = tmp_path / "good.py"
    good.write_text(SHAPES["inside_the_brackets_after_a_comma"][0], encoding="utf-8")
    assert gate.main([str(good)]) == 0
    assert gate.main([str(good), str(bad)]) == 1
    assert "bad.py:3" in capsys.readouterr().err


def test_every_pragma_under_vera_is_filed_under_its_own_line() -> None:
    assert gate.main([]) == 0


# ---------------------------------------------------------------------------
# The differential against mutmut's own visitor, where mutmut is installed
# ---------------------------------------------------------------------------


def _engine_lines(source: str) -> set[int]:
    """The lines mutmut 3.8's `PragmaVisitor` marks in `source`: the
    no-mutate lines and the lines a `block` pragma ignores whole (a header's
    `block` goes to `ignore_node_lines`, the header's line among them)."""
    cst = pytest.importorskip("libcst")
    handling = pytest.importorskip("mutmut.mutation.pragma_handling")
    visitor = handling.PragmaVisitor("<shape>")
    cst.MetadataWrapper(cst.parse_module(source)).visit(visitor)
    return set(visitor.no_mutate_lines) | set(visitor.ignore_node_lines)


def _gate_lines(source: str) -> set[int]:
    """The same, as the gate reads it: each pragma's line where the engine
    files it (a `start` ... `end` or `block` region is not expanded here)."""
    return {p.filed for p in gate.pragmas(source) if p.filed is not None}


def _has_region(source: str) -> bool:
    return any(p.token in ("start", "end", "block") and p.filed is not None for p in gate.pragmas(source))


@pytest.mark.parametrize("name", sorted(SHAPES))
def test_the_gate_reads_each_shape_as_the_engine_does(name: str) -> None:
    """Equal where no region the engine reads is open; with one, each line
    the gate files a pragma under is one the engine marks.  A pragma no
    visitor reads marks nothing."""
    source = SHAPES[name][0]
    if _has_region(source):
        assert _gate_lines(source) <= _engine_lines(source)
    else:
        assert _gate_lines(source) == _engine_lines(source)


def test_the_gate_reads_every_pragma_under_vera_as_the_engine_does() -> None:
    """Over every file of `vera/` that holds a pragma: each line the gate
    files a pragma under is one the engine marks, and with no `start`/`end`
    region in the file the two sets are equal."""
    checked = 0
    for path in gate.iter_scope_files():
        source = path.read_text(encoding="utf-8")
        found = gate.pragmas(source)
        if not found:
            continue
        engine = _engine_lines(source)
        mine = _gate_lines(source)
        assert mine <= engine, (path, sorted(mine - engine))
        if not _has_region(source):
            assert mine == engine, (path, sorted(engine ^ mine))
        checked += 1
    assert checked > 0
