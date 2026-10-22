"""A run-level conformance program's run reaches what its header names
(#1645).

A run-level program is the spec's end-to-end evidence that the features its
header names work, and its manifest entry pins what `vera run` prints.  That
evidence covers only what the run reaches.  For each program #1645 lists,
two cells hold the run to the program:

* every function the program defines is reachable from the function
  `vera run` executes (`main`), through the calls the program writes;
* every built-in function the entry's `features` names is called from a
  function the run reaches.

Reachability is read from the parsed program.  A call is one by the rule
every corpus walk shares (`vera.obligations.cache.called_name`): a bare
call, or one qualified by the program's own module path, which names the
file's own function.  Its name resolves to a `where` helper of an enclosing
function before a top-level one, as the checker resolves it.  What the cells cannot see is a check too
weak to tell a wrong value from a right one, or a header naming a feature
the file does not contain; #1645's lines name those, and each program's
`main` prints, for each case, the value it computed, which the entry's
`expected_stdout` pins.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast
from vera.builtins import BUILTINS
from vera.obligations.cache import called_name, walk_nodes
from vera.resolver import own_module_path

ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE = ROOT / "tests" / "conformance"
MANIFEST: dict[str, dict[str, object]] = {
    entry["id"]: entry
    for entry in json.loads(
        (CONFORMANCE / "manifest.json").read_text(encoding="utf-8"))
}

#: The run-level programs #1645 lists, by manifest id.  (Its line for
#: `ch04_nat_int_widening` names a program deleted in v0.2.3, with the
#: widening it tested.)
LISTED: tuple[str, ...] = (
    # No `main`: `vera run` executed only the first public function.
    "ch04_string_ordering", "ch09_abilities", "ch09_array_utilities",
    "ch09_html", "ch09_json_accessors", "ch09_recursive_show_hash",
    "ch09_show_hash_composites", "ch09_string_char_utilities",
    # A `main` that called none of the tests, or whose check could not fail.
    "ch09_structural_eq", "ch07_state_old_composite", "ch02_builtin_types",
    "ch07_state_new_family",
    # A `main` that ran one case of several.
    "ch04_arithmetic", "ch04_comparison", "ch04_boolean_ops", "ch04_if_else",
    "ch04_let_binding", "ch04_match_basic", "ch04_string_builtins",
    "ch02_option_result", "ch03_slot_indexing", "ch04_nat_binding",
    "ch09_numeric_builtins", "ch09_type_conversions", "ch09_string_search",
    "ch09_float_predicates", "ch04_array_construction",
    "ch07_state_composite", "ch07_exn_composite",
    "ch02_adt_single_letter_name",
    # A header naming features the file did not contain.
    "ch01_string_escapes", "ch04_string_interpolation",
    "ch07_exn_param_alias",
    # A check too weak to see a wrong value.
    "ch01_byte_literals", "ch06_requires_adt_arg", "ch05_nested_closures",
    "ch05_capture_array_index", "ch09_nested_helper_family_op_name",
    "ch09_url_parsing",
    "ch09_generic_where_helper", "ch09_generic_infer_user_fn_return",
)

#: Functions a listed program defines that its run does not reach, each
#: with why it exists: one the check or verify stage is about.
CHECK_ONLY: dict[tuple[str, str], str] = {}


def _program(entry_id: str) -> tuple[ast.Program, tuple[str, ...] | None]:
    """The program, and the path a module-qualified call names its own file
    by (`own_module_path`), which only a `module` declaration gives."""
    path = CONFORMANCE / str(MANIFEST[entry_id]["file"])
    program = pipeline.parse(path).program
    if program.module is None:
        return program, None
    checked = pipeline.check(path)
    return checked.program, own_module_path(
        checked.program, None, checked.resolved or ())


def _functions(program: ast.Program) -> dict[str, ast.FnDecl]:
    """Every function the program defines, a `where` helper keyed below its
    owner (`owner.helper`)."""
    out: dict[str, ast.FnDecl] = {}

    def add(decl: ast.FnDecl, prefix: str) -> None:
        out[prefix + decl.name] = decl
        for helper in decl.where_fns or ():
            add(helper, f"{prefix}{decl.name}.")

    for tld in program.declarations:
        if isinstance(tld.decl, ast.FnDecl):
            add(tld.decl, "")
    return out


def _calls(decl: ast.FnDecl, own: tuple[str, ...] | None) -> set[str]:
    return {name for node in walk_nodes(decl.body)
            if (name := called_name(node, own)) is not None}


def _run(
    program: ast.Program, own: tuple[str, ...] | None,
) -> tuple[set[str], set[str]]:
    """(the functions the run reaches, the names they call), from `main`;
    *own* is the program's own module path."""
    functions = _functions(program)
    reached: set[str] = set()
    called: set[str] = set()
    todo = ["main"]
    while todo:
        key = todo.pop()
        if key in reached:
            continue
        reached.add(key)
        names = _calls(functions[key], own)
        called |= names
        scope = key.split(".")
        for name in names:
            for depth in range(len(scope), -1, -1):
                candidate = ".".join([*scope[:depth], name])
                if candidate in functions:
                    todo.append(candidate)
                    break
    return reached, called


@pytest.mark.parametrize("entry_id", LISTED)
def test_the_run_reaches_every_function_the_program_defines(
    entry_id: str,
) -> None:
    program, own = _program(entry_id)
    functions = _functions(program)
    assert "main" in functions, f"{entry_id} has no `main` for `vera run`"
    reached, _ = _run(program, own)
    unreached = sorted(
        name for name in set(functions) - reached
        if (entry_id, name) not in CHECK_ONLY)
    assert not unreached, (
        f"`vera run` of {entry_id} never reaches {unreached}")


@pytest.mark.parametrize("entry_id", LISTED)
def test_the_run_calls_every_builtin_the_entry_names(entry_id: str) -> None:
    features = MANIFEST[entry_id].get("features", [])
    assert isinstance(features, list)
    named = [f for f in features if f in BUILTINS]
    _, called = _run(*_program(entry_id))
    assert not [f for f in named if f not in called], (
        f"`vera run` of {entry_id} calls none of "
        f"{[f for f in named if f not in called]}")


def test_every_listed_program_is_a_run_level_entry() -> None:
    assert len(set(LISTED)) == len(LISTED) == 41
    assert {MANIFEST[i]["level"] for i in LISTED} == {"run"}


def test_check_only_names_listed_programs_and_their_functions() -> None:
    """A stale entry would exempt nothing and say it exempts something."""
    for (entry_id, name), why in CHECK_ONLY.items():
        assert entry_id in LISTED and why
        assert name in _functions(_program(entry_id)[0]), (entry_id, name)
