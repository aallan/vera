"""Every host import is total over the inputs its signature accepts (#1502).

A built-in implemented in the host (regex, JSON, HTML, Markdown, Decimal,
and the rest) used to end a verified program with a ``host_error`` trap on
inputs its declared signature accepts: an exception class the host
function did not list, Python's recursion limit in a recursive tree walk,
the ``decimal`` context's trapped signals, CPython's 4,300-digit
integer-string limit, and a fixed shadow-stack window that tree writers
filled with roots in proportion to the tree.  The rule every host import
must now meet:

* a valid input produces a value;
* an input beyond a real limit produces ``Err`` where the type allows it
  (``json_parse`` and ``md_parse`` state their nesting limits, identically
  on both hosts);
* nothing produces a raw host trap.

This module is the instrument for that rule.

1. **Enumeration.**  Every host import is read out of the binding code
   itself, not listed by hand: each ``linker.define_func("vera", ...)``
   in ``vera/codegen/api.py`` and ``vera/runtime/*.py`` (literal names,
   f-string families, names bound from an f-string or a loop over a
   literal table), and each ``imports.vera`` binding in
   ``vera/browser/runtime.mjs`` (dotted and bracketed assignments, the
   binding tables looped into ``imports.vera[name]``, and the
   ``name.match(/^prefix.../)`` families).  :data:`BATTERY` and
   :data:`EXEMPT` together must name exactly that set, so a new host
   import without a battery entry turns this module red, and so does an
   entry for an import that no longer exists.

2. **Battery.**  For each import, adversarial inputs from the #1502
   table — deep nesting, wide trees, invalid and oversized patterns,
   non-finite and extreme decimals, long numerals, huge durations — run
   in a SUBPROCESS (a probe that exhausts the stack or memory must not
   take the test process with it), each asserting the exact output.

3. **Parity.**  The same compiled module runs under the browser runtime
   (Node), and each probe's output must match the Python host's exactly,
   or, for the regex family (whose two engines are different regex
   dialects), must at least be a ``Result`` on both hosts.

An import in :data:`EXEMPT` carries the reason it has no adversarial
input: a trap channel whose whole job is to name a trap, a GC hook with
no Vera-level signature, an effect whose failures already map to its
``Result``, or a known member of the class tracked elsewhere.
"""

from __future__ import annotations

import ast
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
API = ROOT / "vera" / "codegen" / "api.py"
RUNTIME_DIR = ROOT / "vera" / "runtime"
RUNTIME_MJS = ROOT / "vera" / "browser" / "runtime.mjs"
HARNESS = ROOT / "vera" / "browser" / "harness.mjs"


# =====================================================================
# 1. Enumeration from the binding code
# =====================================================================


def _fstring_family(node: ast.JoinedStr) -> str:
    """``f"map_get$k{kt}_v{vt}"`` -> ``"map_get$k*"``."""
    prefix = ""
    for part in node.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            prefix += part.value
        else:
            break
    return prefix + "*"


def _scopes(tree: ast.AST) -> dict[ast.AST, list[ast.AST]]:
    """Map every node to its enclosing function scopes, innermost first."""
    chains: dict[ast.AST, list[ast.AST]] = {}

    def visit(node: ast.AST, chain: list[ast.AST]) -> None:
        chains[node] = chain
        inner = chain
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            inner = [node, *chain]
        for child in ast.iter_child_nodes(node):
            visit(child, inner)

    visit(tree, [tree])
    return chains


def _assigned_values(scope: ast.AST, name: str) -> list[ast.expr]:
    """Values assigned to ``name`` directly in ``scope`` (not nested defs)."""
    values: list[ast.expr] = []
    stack = list(ast.iter_child_nodes(scope))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if isinstance(node, ast.Assign):
            if any(isinstance(t, ast.Name) and t.id == name
                   for t in node.targets):
                values.append(node.value)
        elif isinstance(node, ast.AnnAssign):
            if (isinstance(node.target, ast.Name)
                    and node.target.id == name and node.value is not None):
                values.append(node.value)
        stack.extend(ast.iter_child_nodes(node))
    return values


def _loop_names(scope: ast.AST, name: str, chain: list[ast.AST]) -> set[str]:
    """Names bound to ``name`` by a ``for`` over a literal table."""
    found: set[str] = set()
    for node in ast.walk(scope):
        if not isinstance(node, ast.For):
            continue
        target = node.target
        position = None
        if isinstance(target, ast.Name) and target.id == name:
            position = -1
        elif isinstance(target, ast.Tuple):
            for i, elt in enumerate(target.elts):
                if isinstance(elt, ast.Name) and elt.id == name:
                    position = i
        if position is None or not isinstance(node.iter, ast.Name):
            continue
        for enclosing in chain:
            for value in _assigned_values(enclosing, node.iter.id):
                if not isinstance(value, (ast.Tuple, ast.List)):
                    continue
                for row in value.elts:
                    cell = row
                    if position >= 0 and isinstance(row, (ast.Tuple, ast.List)):
                        cell = row.elts[position]
                    if isinstance(cell, ast.Constant) and isinstance(
                        cell.value, str,
                    ):
                        found.add(cell.value)
    return found


def enumerate_python_host_imports() -> tuple[set[str], list[str]]:
    """Every host import the Python host defines, and any it cannot name."""
    names: set[str] = set()
    unresolved: list[str] = []
    for path in [API, *sorted(RUNTIME_DIR.glob("*.py"))]:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        chains = _scopes(tree)
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Attribute)
                    and node.func.attr == "define_func"
                    and len(node.args) >= 2):
                continue
            module_arg, name_arg = node.args[0], node.args[1]
            if not (isinstance(module_arg, ast.Constant)
                    and module_arg.value == "vera"):
                unresolved.append(f"{path.name}:{node.lineno} (module)")
                continue
            if isinstance(name_arg, ast.Constant) and isinstance(
                name_arg.value, str,
            ):
                names.add(name_arg.value)
                continue
            if isinstance(name_arg, ast.JoinedStr):
                names.add(_fstring_family(name_arg))
                continue
            resolved: set[str] = set()
            if isinstance(name_arg, ast.Name):
                chain = chains[node]
                for scope in chain:
                    for value in _assigned_values(scope, name_arg.id):
                        if isinstance(value, ast.JoinedStr):
                            resolved.add(_fstring_family(value))
                        elif isinstance(value, ast.Constant) and isinstance(
                            value.value, str,
                        ):
                            resolved.add(value.value)
                    if resolved:
                        break
                if not resolved:
                    for scope in chain:
                        resolved |= _loop_names(scope, name_arg.id, chain)
                        if resolved:
                            break
            if resolved:
                names |= resolved
            else:
                unresolved.append(f"{path.name}:{node.lineno}")
    return names, unresolved


_JS_REGEX_FAMILY = re.compile(r"name\.match\(/\^((?:[^/\\]|\\.)*)/\)")


def _build_import_object_body(src: str) -> str:
    """The text of ``buildImportObject``, where every binding is made."""
    start = src.index("function buildImportObject(")
    end = src.index("\n}\n", start)
    return src[start:end]


def enumerate_browser_host_imports() -> set[str]:
    """Every host import ``vera/browser/runtime.mjs`` binds."""
    src = RUNTIME_MJS.read_text(encoding="utf-8")
    body_text = _build_import_object_body(src)
    names = set(re.findall(
        r"imports\.vera\.([A-Za-z_$][\w$]*)\s*=(?!=)", body_text,
    ))
    names |= set(re.findall(
        r"imports\.vera\[\s*[\"']([^\"']+)[\"']\s*\]\s*=(?!=)", body_text,
    ))
    for table in set(re.findall(
        r"for \(const \[name, fn\] of Object\.entries\((\w+)\)\)", body_text,
    )):
        body = re.search(
            r"const " + re.escape(table) + r"\s*=\s*\{(.*?)\};", src, re.S,
        )
        assert body is not None, f"binding table {table} not found"
        names |= set(re.findall(r"^\s*([A-Za-z_]\w*)\s*:", body.group(1), re.M))
    for pattern in _JS_REGEX_FAMILY.findall(body_text):
        literal = pattern.split("(", 1)[0]
        literal = re.sub(r"\\(.)", r"\1", literal)
        names.add(literal[:-1] if "(" not in pattern else literal + "*")
    return names


# =====================================================================
# 2. The battery
# =====================================================================

# Each family is one Vera program: helpers, then one public probe per
# adversarial input, printing the result so both hosts compare stdout.
_HELPERS: dict[str, str] = {
    "regex": """
private fn show_rb(@Result<Bool, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Result<Bool, String>.0 {
    Ok(@Bool) -> if @Bool.0 then { "Ok(true)" } else { "Ok(false)" },
    Err(@String) -> string_concat("Err: ", @String.0)
  }
}

private fn show_rs(@Result<String, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Result<String, String>.0 {
    Ok(@String) -> string_concat("Ok: ", @String.0),
    Err(@String) -> string_concat("Err: ", @String.0)
  }
}

private fn show_ro(@Result<Option<String>, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Result<Option<String>, String>.0 {
    Ok(@Option<String>) -> match @Option<String>.0 {
      Some(@String) -> string_concat("Ok(Some): ", @String.0),
      None -> "Ok(None)"
    },
    Err(@String) -> string_concat("Err: ", @String.0)
  }
}

private fn show_ra(@Result<Array<String>, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Result<Array<String>, String>.0 {
    Ok(@Array<String>) -> string_concat("Ok: ", int_to_string(array_length(@Array<String>.0))),
    Err(@String) -> string_concat("Err: ", @String.0)
  }
}

private fn nested_groups(@Int -> @String)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{
  string_concat(string_concat(string_repeat("(", @Int.0), "a"), string_repeat(")", @Int.0))
}
""",
    "json": """
private fn show_rj(@Result<Json, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Result<Json, String>.0 {
    Ok(@Json) -> string_concat("Ok: ", json_type(@Json.0)),
    Err(@String) -> string_concat("Err: ", @String.0)
  }
}

private fn nested_arrays(@Int -> @String)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{
  string_concat(string_repeat("[", @Int.0), string_repeat("]", @Int.0))
}

private fn wrap_json(@Nat, @Json -> @Json)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @Json.0 } else { wrap_json(@Nat.0 - 1, JArray([@Json.0])) }
}

private fn flat_objects(@Int -> @String)
  requires(@Int.0 >= 1) ensures(true) effects(pure)
{
  string_concat(string_concat("[", string_repeat("{\\"k\\": 1},", @Int.0 - 1)), "{\\"k\\": 1}]")
}
""",
    "markdown": """
private fn show_rm(@Result<MdBlock, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> string_concat("Ok: ", int_to_string(string_length(md_render(@MdBlock.0)))),
    Err(@String) -> string_concat("Err: ", @String.0)
  }
}

private fn quotes(@Int -> @String)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{
  string_concat(string_repeat("> ", @Int.0), "x")
}

private fn links(@Int -> @String)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{
  string_concat(string_concat(string_repeat("[", @Int.0), "x"), string_repeat("](u)", @Int.0))
}

private fn wrap_quote(@Nat, @MdBlock -> @MdBlock)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @MdBlock.0 } else { wrap_quote(@Nat.0 - 1, MdBlockQuote([@MdBlock.0])) }
}

private fn wrap_emph(@Nat, @MdInline -> @MdInline)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @MdInline.0 } else { wrap_emph(@Nat.0 - 1, MdEmph([@MdInline.0])) }
}

private fn yes_no(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { "true" } else { "false" }
}
""",
    "html": """
private fn wrap_b(@Nat, @HtmlNode -> @HtmlNode)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @HtmlNode.0 } else { wrap_b(@Nat.0 - 1, HtmlElement("b", map_new(), [@HtmlNode.0])) }
}
""",
    "decimal": """
private fn show_od(@Option<Decimal> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Decimal>.0 {
    Some(@Decimal) -> string_concat("Some ", decimal_to_string(@Decimal.0)),
    None -> "None"
  }
}

private fn show_ord(@Ordering -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Ordering.0 {
    Less -> "Less",
    Equal -> "Equal",
    Greater -> "Greater"
  }
}

private fn inf(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  decimal_from_float(infinity())
}

private fn big(@String -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  match decimal_from_string(@String.0) {
    Some(@Decimal) -> @Decimal.0,
    None -> decimal_from_int(0)
  }
}
""",
    "io": "",
    "collections": "",
}


@dataclass(frozen=True)
class Probe:
    """One adversarial input: a Vera ``String`` expression and its output.

    ``parity`` is how the browser host is held to the Python host:
    ``"exact"`` (same stdout), ``"result"`` (both print an ``Ok`` or an
    ``Err``), or ``"none"`` with the documented reason in :data:`NO_PARITY`.
    """

    family: str
    name: str
    expr: str
    expect: str
    parity: str = "exact"


_JSON_DEPTH_ERR = (
    "Err: json_parse: the text nests arrays and objects more than 512 "
    "levels deep — RFC 8259 §9 lets an implementation set a maximum "
    "nesting depth, and Vera's is 512.  Flatten the structure, or split "
    "the document."
)
_JSON_OVERFLOW_ERR = (
    "Err: json_parse: a number in the text overflows to Infinity, which "
    "JSON cannot represent — RFC 8259 §6 lets an implementation set limits "
    "on the range of numbers it accepts, and Vera's accepted range is the "
    "finite Float64 values.  Keep the magnitude at or below "
    "1.7976931348623157e308, or carry the value as a string."
)
_MD_NESTING_ERR = (
    "Err: md_parse: the text nests blocks and inline spans more than 512 "
    "levels deep, which is Vera's limit.  Flatten the structure."
)

PROBES: tuple[Probe, ...] = (
    # --- regex: every failure of the host's regex work is the Err arm.
    Probe("regex", "match_big_repeat",
          'show_rb(regex_match("a", "a{4294967296}"))',
          "Err: invalid regex: the repetition number is too large", "result"),
    Probe("regex", "find_big_repeat",
          'show_ro(regex_find("a", "a{4294967296}"))',
          "Err: invalid regex: the repetition number is too large", "result"),
    Probe("regex", "find_all_big_repeat",
          'show_ra(regex_find_all("a", "a{4294967296}"))',
          "Err: invalid regex: the repetition number is too large", "result"),
    Probe("regex", "replace_big_repeat",
          'show_rs(regex_replace("a", "a{4294967296}", "b"))',
          "Err: invalid regex: the repetition number is too large", "result"),
    Probe("regex", "match_deep_groups",
          'show_rb(regex_match("a", nested_groups(1000)))',
          "Err: invalid regex: the pattern nests too deeply to compile",
          "result"),
    Probe("regex", "find_deep_groups",
          'show_ro(regex_find("a", nested_groups(1000)))',
          "Err: invalid regex: the pattern nests too deeply to compile",
          "result"),
    Probe("regex", "find_all_deep_groups",
          'show_ra(regex_find_all("a", nested_groups(1000)))',
          "Err: invalid regex: the pattern nests too deeply to compile",
          "result"),
    Probe("regex", "replace_unknown_group",
          'show_rs(regex_replace("abc", "b", "\\\\g<foo>"))',
          "Err: invalid regex: unknown group name 'foo'", "result"),
    # --- json_parse: valid input parses; past a real limit, the pinned Err.
    Probe("json", "flat_2500_objects",
          'match json_parse(flat_objects(2500)) { '
          'Ok(@Json) -> string_concat("Ok: ", '
          'int_to_string(json_array_length(@Json.0))), '
          'Err(@String) -> string_concat("Err: ", @String.0) }',
          "Ok: 2500"),
    # Wide enough that a writer keeping even one root per object (a
    # map wrapper each) would exhaust the 4,096-root window: the
    # 2,500-object case above no longer can, so it alone would not
    # notice a writer that stopped releasing.
    Probe("json", "flat_5000_objects",
          'match json_parse(flat_objects(5000)) { '
          'Ok(@Json) -> string_concat("Ok: ", '
          'int_to_string(json_array_length(@Json.0))), '
          'Err(@String) -> string_concat("Err: ", @String.0) }',
          "Ok: 5000"),
    Probe("json", "depth_512", "show_rj(json_parse(nested_arrays(512)))",
          "Ok: array"),
    Probe("json", "depth_513", "show_rj(json_parse(nested_arrays(513)))",
          _JSON_DEPTH_ERR),
    Probe("json", "depth_100000",
          "show_rj(json_parse(nested_arrays(100000)))", _JSON_DEPTH_ERR),
    Probe("json", "integer_5000_digits",
          'show_rj(json_parse(string_concat("1", string_repeat("0", 5000))))',
          _JSON_OVERFLOW_ERR),
    # --- json_stringify: a total signature over a tree built in Vera.
    Probe("json", "stringify_20000_deep",
          "int_to_string(string_length(json_stringify(wrap_json(20000, JNull))))",
          "40004"),
    # --- md_parse: valid input parses; past the stated limit, the pinned Err.
    Probe("markdown", "quotes_500", "show_rm(md_parse(quotes(500)))",
          "Ok: 1001"),
    Probe("markdown", "quotes_512", "show_rm(md_parse(quotes(512)))",
          "Ok: 1025"),
    Probe("markdown", "quotes_513", "show_rm(md_parse(quotes(513)))",
          _MD_NESTING_ERR),
    Probe("markdown", "links_513", "show_rm(md_parse(links(513)))",
          _MD_NESTING_ERR),
    Probe("markdown", "flat_5000_paragraphs",
          'show_rm(md_parse(string_repeat("p *e*\\n\\n", 5000)))',
          "Ok: 34998"),
    # --- md_render and the queries: total over trees built in Vera.
    Probe("markdown", "render_20000_quotes",
          'int_to_string(string_length(md_render(wrap_quote(20000, '
          'MdParagraph([MdText("x")])))))',
          "40001"),
    Probe("markdown", "render_20000_emphasis",
          'int_to_string(string_length(md_render(MdParagraph([wrap_emph('
          '20000, MdText("x"))]))))',
          "40001"),
    Probe("markdown", "has_heading_20000",
          'yes_no(md_has_heading(wrap_quote(20000, MdHeading(2, '
          '[MdText("h")])), 2))',
          "true"),
    Probe("markdown", "has_code_block_20000",
          'yes_no(md_has_code_block(wrap_quote(20000, '
          'MdCodeBlock("py", "c")), "py"))',
          "true"),
    Probe("markdown", "extract_20000",
          'int_to_string(array_length(md_extract_code_blocks(wrap_quote('
          '20000, MdCodeBlock("py", "c")), "py")))',
          "1"),
    # --- HTML: total walks over trees built in Vera; html_parse's Err.
    Probe("html", "query_chain_100",
          'int_to_string(array_length(html_query(wrap_b(100, '
          'HtmlText("x")), "b")))',
          "100"),
    Probe("html", "query_top_of_3000",
          'int_to_string(array_length(html_query(HtmlElement("i", '
          'map_new(), [wrap_b(3000, HtmlText("x"))]), "i")))',
          "1"),
    Probe("html", "to_string_3000",
          'int_to_string(string_length(html_to_string(wrap_b(3000, '
          'HtmlText("x")))))',
          "21001"),
    Probe("html", "text_3000", 'html_text(wrap_b(3000, HtmlText("x")))',
          "x"),
    Probe("html", "parse_5000_deep",
          'match html_parse(string_concat(string_repeat("<b>", 5000), "x")) '
          '{ Ok(@HtmlNode) -> string_concat("Ok: ", html_text(@HtmlNode.0)), '
          'Err(@String) -> "Err" }',
          "Ok: x", "none"),
    Probe("html", "parse_5000_flat",
          'match html_parse(string_repeat("<p class=\\"c\\">t</p>", 5000)) '
          '{ Ok(@HtmlNode) -> string_concat("Ok: ", int_to_string('
          'string_length(html_text(@HtmlNode.0)))), '
          'Err(@String) -> "Err" }',
          "Ok: 5000", "none"),
    # --- Decimal: one fixed, non-trapping context; exact answers.
    Probe("decimal", "add_inf_neg_inf",
          "decimal_to_string(decimal_add(inf(()), decimal_neg(inf(()))))",
          "NaN", "none"),
    Probe("decimal", "sub_inf_inf",
          "decimal_to_string(decimal_sub(inf(()), inf(())))", "NaN", "none"),
    Probe("decimal", "mul_inf_zero",
          "decimal_to_string(decimal_mul(inf(()), decimal_from_int(0)))",
          "NaN", "none"),
    Probe("decimal", "div_inf_inf", "show_od(decimal_div(inf(()), inf(())))",
          "Some NaN", "none"),
    Probe("decimal", "compare_nan_one",
          "show_ord(decimal_compare(decimal_from_float(nan()), "
          "decimal_from_int(1)))",
          "Greater", "none"),
    Probe("decimal", "eq_nan_nan",
          "if decimal_eq(decimal_from_float(nan()), decimal_from_float(nan())) "
          'then { "true" } else { "false" }',
          "false", "none"),
    Probe("decimal", "neg_huge",
          'decimal_to_string(decimal_neg(big("12345e999999")))',
          "-1.2345E+1000003"),
    Probe("decimal", "abs_huge",
          'decimal_to_string(decimal_abs(big("-12345e999999")))',
          "1.2345E+1000003"),
    Probe("decimal", "round_inf",
          "decimal_to_string(decimal_round(inf(()), 2))", "Infinity",
          "none"),
    Probe("decimal", "from_string_5000_digit_exponent",
          'show_od(decimal_from_string(string_concat("1e", '
          'string_repeat("0", 5000))))',
          "Some 1"),
    Probe("decimal", "to_float_inf",
          "float_to_string(decimal_to_float(inf(())))", "inf"),
    Probe("decimal", "from_int_min",
          "decimal_to_string(decimal_from_int(0 - 9223372036854775807))",
          "-9223372036854775807"),
    # --- IO.sleep: a Nat of any size is a duration to honour.
    Probe("io", "sleep_1e13_ms",
          'IO.sleep(10000000000000); "slept"', "slept", "none"),
    # --- Map / Set: NaN keys and elements, and a 2,000-entry container.
    Probe("collections", "map_ops",
          "map_summary(())", "2000 true 2 1999 1999 3", "exact"),
    Probe("collections", "set_ops",
          "set_summary(())", "2 true false 1", "exact"),
)

NO_PARITY: dict[str, str] = {
    "parse_5000_deep": (
        "html_parse needs DOMParser; under Node the browser runtime returns "
        "its documented Unsupported-runtime Err"
    ),
    "parse_5000_flat": "as parse_5000_deep",
    "add_inf_neg_inf": (
        "non-finite Decimal arithmetic is outside the browser engine's "
        "parity domain (spec §9.7.2)"
    ),
    "sub_inf_inf": "as add_inf_neg_inf",
    "mul_inf_zero": "as add_inf_neg_inf",
    "div_inf_inf": "as add_inf_neg_inf",
    "compare_nan_one": "as add_inf_neg_inf",
    "eq_nan_nan": "as add_inf_neg_inf",
    "round_inf": "as add_inf_neg_inf",
    "sleep_1e13_ms": (
        "the Python probe replaces time.sleep; the browser's sleep busy-waits"
    ),
}

_COLLECTIONS_SRC = """
private fn fill(@Nat, @Map<Int, Int> -> @Map<Int, Int>)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @Map<Int, Int>.0 } else { fill(@Nat.0 - 1, map_insert(@Map<Int, Int>.0, nat_to_int(@Nat.0), 1)) }
}

private fn map_summary(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = fill(2000, map_new());
  let @Map<Float64, Int> = map_insert(map_insert(map_new(), nan(), 1), nan(), 2);
  let @Map<String, Int> = map_insert(map_insert(map_insert(map_new(), "a", 1), "b", 2), "c", 3);
  string_join([
    int_to_string(map_size(@Map<Int, Int>.0)),
    if map_contains(@Map<Float64, Int>.0, nan()) then { "true" } else { "false" },
    match map_get(@Map<Float64, Int>.0, nan()) { Some(@Int) -> int_to_string(@Int.0), None -> "none" },
    int_to_string(map_size(map_remove(@Map<Int, Int>.0, 7))),
    int_to_string(array_length(map_keys(map_remove(@Map<Int, Int>.0, 8)))),
    int_to_string(array_length(map_values(@Map<String, Int>.0)))
  ], " ")
}

private fn set_summary(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Float64> = set_add(set_add(set_add(set_new(), nan()), nan()), 1.0);
  let @Set<String> = set_add(set_new(), "s");
  string_join([
    int_to_string(set_size(@Set<Float64>.0)),
    if set_contains(@Set<Float64>.0, nan()) then { "true" } else { "false" },
    if set_contains(set_remove(@Set<String>.0, "s"), "s") then { "true" } else { "false" },
    int_to_string(array_length(set_to_array(@Set<String>.0)))
  ], " ")
}
"""
_HELPERS["collections"] = _COLLECTIONS_SRC

#: Which probes cover each host import.  The keys are exactly the imports
#: the two binding tables name, minus :data:`EXEMPT`.
BATTERY: dict[str, tuple[str, ...]] = {
    "regex_match": ("match_big_repeat", "match_deep_groups"),
    "regex_find": ("find_big_repeat", "find_deep_groups"),
    "regex_find_all": ("find_all_big_repeat", "find_all_deep_groups"),
    "regex_replace": ("replace_big_repeat", "replace_unknown_group"),
    "json_parse": ("flat_2500_objects", "flat_5000_objects", "depth_512",
                   "depth_513",
                   "depth_100000", "integer_5000_digits"),
    "json_stringify": ("stringify_20000_deep",),
    "md_parse": ("quotes_500", "quotes_512", "quotes_513", "links_513",
                 "flat_5000_paragraphs"),
    "md_render": ("render_20000_quotes", "render_20000_emphasis"),
    "md_has_heading": ("has_heading_20000",),
    "md_has_code_block": ("has_code_block_20000",),
    "md_extract_code_blocks": ("extract_20000",),
    "html_parse": ("parse_5000_deep", "parse_5000_flat"),
    "html_to_string": ("to_string_3000",),
    "html_text": ("text_3000",),
    "html_query": ("query_chain_100", "query_top_of_3000"),
    "decimal_add": ("add_inf_neg_inf",),
    "decimal_sub": ("sub_inf_inf",),
    "decimal_mul": ("mul_inf_zero",),
    "decimal_div": ("div_inf_inf",),
    "decimal_compare": ("compare_nan_one",),
    "decimal_eq": ("eq_nan_nan",),
    "decimal_neg": ("neg_huge",),
    "decimal_abs": ("abs_huge",),
    "decimal_round": ("round_inf",),
    "decimal_from_string": ("from_string_5000_digit_exponent",),
    "decimal_from_float": ("add_inf_neg_inf", "compare_nan_one"),
    "decimal_from_int": ("from_int_min",),
    "decimal_to_string": ("sub_inf_inf",),
    "decimal_to_float": ("to_float_inf",),
    "sleep": ("sleep_1e13_ms",),
    "map_new": ("map_ops",),
    "map_size": ("map_ops",),
    "map_insert$k*": ("map_ops",),
    "map_get$k*": ("map_ops",),
    "map_contains$k*": ("map_ops",),
    "map_remove$k*": ("map_ops",),
    "map_keys$k*": ("map_ops",),
    "map_values$v*": ("map_ops",),
    "set_new": ("set_ops",),
    "set_size": ("set_ops",),
    "set_add$e*": ("set_ops",),
    "set_contains$e*": ("set_ops",),
    "set_remove$e*": ("set_ops",),
    "set_to_array$e*": ("set_ops",),
}

_EFFECT_RESULT = (
    "an effect operation that returns a Result or Option; every failure of "
    "the environment already becomes its Err or None at the host boundary "
    "(its `except Exception`), and exercising it needs a network, a "
    "database or a provider key"
)
_TRAP_CHANNEL = "a trap channel: its whole job is to name a trap"
_GC_HOOK = "a collector hook with no Vera-level signature"
_TOTAL_IO = (
    "moves a value the guest already holds, or reads the environment; no "
    "argument value makes the host raise"
)
_MATH = (
    "math: every out-of-domain input already returns NaN or -Infinity "
    "(IEEE 754), pinned by the math tests"
)

EXEMPT: dict[str, str] = {
    "print": _TOTAL_IO,
    "stderr": _TOTAL_IO,
    "read_line": _TOTAL_IO,
    "read_char": _TOTAL_IO,
    "read_file": _EFFECT_RESULT,
    "write_file": _EFFECT_RESULT,
    "args": _TOTAL_IO,
    "get_env": _TOTAL_IO,
    "time": _TOTAL_IO,
    "exit": "ends the program by design (the exit channel), with the code given",
    "contract_fail": _TRAP_CHANNEL,
    "overflow_trap": _TRAP_CHANNEL,
    "nat_guard_trap": _TRAP_CHANNEL,
    "widen_trap": _TRAP_CHANNEL,
    "host_decref_handle": _GC_HOOK,
    "attach_bucket_to_wrapper": _GC_HOOK,
    "state_get_*": _TOTAL_IO,
    "state_put_*": _TOTAL_IO,
    "state_push_*": _TOTAL_IO,
    "state_pop_*": _TOTAL_IO,
    "http_get": _EFFECT_RESULT,
    "http_post": _EFFECT_RESULT,
    "async_http_get": _EFFECT_RESULT,
    "async_http_post": _EFFECT_RESULT,
    "async_await": _EFFECT_RESULT,
    "inference_complete": _EFFECT_RESULT,
    "db_query": _EFFECT_RESULT,
    "db_execute": _EFFECT_RESULT,
    "random_float": "Random: no argument",
    "random_bool": "Random: no argument",
    "random_int": (
        "KNOWN MEMBER, not fixed here: both hosts raise for low > high, a "
        "precondition spec §7.7.4 states and nothing obligates; the fix is a "
        "verifier obligation for the built-in's domain, the mechanism PR "
        "#1486 introduces"
    ),
    "log": _MATH, "log2": _MATH, "log10": _MATH, "sin": _MATH,
    "cos": _MATH, "tan": _MATH, "asin": _MATH, "acos": _MATH,
    "atan": _MATH, "atan2": _MATH,
}


def _program(family: str) -> str:
    probes = [p for p in PROBES if p.family == family]
    effects = "<IO>"
    parts = [_HELPERS[family]]
    for p in probes:
        parts.append(
            f"public fn {p.name}(@Unit -> @Unit)\n"
            f"  requires(true) ensures(true) effects({effects})\n"
            f"{{\n  IO.print({p.expr})\n}}\n"
            if not p.expr.startswith("IO.sleep") else
            f"public fn {p.name}(@Unit -> @Unit)\n"
            f"  requires(true) ensures(true) effects({effects})\n"
            f"{{\n  {p.expr.split(';')[0]};\n"
            f"  IO.print({p.expr.split(';')[1].strip()})\n}}\n"
        )
    return "\n".join(parts)


# The subprocess driver: compile once, run each probe, one JSON line each.
# ``--no-sleep`` makes every sleep the host asks for that ``time.sleep``
# can represent return at once, so the sleep probe can honour a Nat of
# 10**13 ms without waiting for it; a duration past that is still handed
# to the real ``time.sleep``, which refuses it with ``OverflowError`` at
# once, exactly as it did for the host before #1502.
_DRIVER = r"""
import json, sys, time
from pathlib import Path
# Cap the memory a probe can WRITE (Linux 4.7+ counts private writable
# mappings against RLIMIT_DATA).  Not RLIMIT_AS: wasmtime reserves
# several GiB of address space per linear memory up front, so a cap on
# the address space small enough to matter would stop the module from
# instantiating.  macOS does not enforce it; Windows has no resource.
if sys.platform.startswith("linux"):
    import resource
    _soft, _hard = resource.getrlimit(resource.RLIMIT_DATA)
    _cap = 4 << 30
    if _hard != resource.RLIM_INFINITY:
        _cap = min(_cap, _hard)
    resource.setrlimit(resource.RLIMIT_DATA, (_cap, _hard))
if sys.argv[1] == "--no-sleep":
    _real_sleep = time.sleep
    time.sleep = lambda seconds: _real_sleep(0 if seconds <= 1e9 else seconds)
    del sys.argv[1]
import vera
print(json.dumps({"canary": vera.__file__}), flush=True)
from vera.checker import typecheck
from vera.codegen import compile as codegen_compile, execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_file
from vera.transform import transform
path = Path(sys.argv[1])
src = path.read_text(encoding="utf-8")
ast = transform(parse_file(str(path)))
diags = typecheck(ast, src, file=str(path))
errors = [d.description for d in diags if d.severity == "error"]
if errors:
    print(json.dumps({"compile_error": errors}), flush=True)
    sys.exit(0)
result = codegen_compile(ast, source=src, file=str(path))
if not result.ok:
    print(json.dumps({"compile_error": [str(d) for d in result.diagnostics]}), flush=True)
    sys.exit(0)
Path(sys.argv[2]).write_bytes(result.wasm_bytes)
for fn in sys.argv[3:]:
    try:
        r = execute(result, fn_name=fn, args=[])
        print(json.dumps({"fn": fn, "ok": True, "stdout": r.stdout}), flush=True)
    except WasmTrapError as exc:
        print(json.dumps({"fn": fn, "ok": False, "kind": exc.kind, "message": str(exc)[:400]}), flush=True)
"""


def _child_env() -> dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env["PYTHONPATH"] = str(ROOT) + os.pathsep + env.get("PYTHONPATH", "")
    return env


def _run_family(family: str, tmp: Path) -> tuple[dict[str, dict[str, object]], Path]:
    source = tmp / f"{family}.vera"
    source.write_text(_program(family), encoding="utf-8")
    wasm = tmp / f"{family}.wasm"
    names = [p.name for p in PROBES if p.family == family]
    cmd = [sys.executable, "-c", _DRIVER]
    if family == "io":
        cmd.append("--no-sleep")
    cmd += [str(source), str(wasm), *names]
    proc = subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8",
        timeout=600, check=False, cwd=str(tmp), env=_child_env(),
    )
    lines = [json.loads(line) for line in proc.stdout.splitlines()
             if line.startswith("{")]
    assert lines, f"{family}: driver produced nothing\n{proc.stderr[-2000:]}"
    canary = lines[0].get("canary", "")
    assert Path(str(canary)).resolve().is_relative_to(ROOT), (
        f"{family}: probes ran against {canary}, not this checkout"
    )
    assert "compile_error" not in lines[1], f"{family}: {lines[1]}"
    return {str(d["fn"]): d for d in lines[1:]}, wasm


# =====================================================================
# Tests
# =====================================================================


def test_enumeration_resolves_every_python_binding() -> None:
    names, unresolved = enumerate_python_host_imports()
    assert not unresolved, (
        "define_func sites whose import name the instrument cannot read: "
        f"{unresolved}.  Name the import with a literal, an f-string, or a "
        "loop over a literal table, or teach the enumeration the new shape."
    )
    # A floor, so an enumeration that silently finds nothing is red.
    assert len(names) > 60


def test_every_python_host_import_has_a_battery_entry() -> None:
    names, _ = enumerate_python_host_imports()
    covered = set(BATTERY) | set(EXEMPT)
    assert names - covered == set(), (
        f"host imports with no battery entry: {sorted(names - covered)}"
    )
    assert covered - names - _browser_only() == set(), (
        f"battery entries for imports neither host defines: "
        f"{sorted(covered - names - _browser_only())}"
    )


def _browser_only() -> set[str]:
    return enumerate_browser_host_imports() - enumerate_python_host_imports()[0]


def test_every_browser_host_import_has_a_battery_entry() -> None:
    names = enumerate_browser_host_imports()
    assert len(names) > 60
    covered = set(BATTERY) | set(EXEMPT)
    assert names - covered == set(), (
        f"browser host imports with no battery entry: {sorted(names - covered)}"
    )


def test_battery_entries_name_real_probes() -> None:
    probe_names = {p.name for p in PROBES}
    assert len(probe_names) == len(PROBES), "probe names must be unique"
    for imp, probes in BATTERY.items():
        assert probes, imp
        assert set(probes) <= probe_names, (imp, set(probes) - probe_names)
    assert not set(BATTERY) & set(EXEMPT)
    for p in PROBES:
        assert (p.parity == "none") == (p.name in NO_PARITY), p.name


_FAMILIES = sorted({p.family for p in PROBES})


@pytest.fixture(scope="module")
def python_outcomes(
    tmp_path_factory: pytest.TempPathFactory,
) -> dict[str, tuple[dict[str, dict[str, object]], Path]]:
    tmp = tmp_path_factory.mktemp("host_totality")
    return {family: _run_family(family, tmp) for family in _FAMILIES}


@pytest.mark.parametrize("probe", PROBES, ids=lambda p: p.name)
def test_probe_on_python_host(
    probe: Probe,
    python_outcomes: dict[str, tuple[dict[str, dict[str, object]], Path]],
) -> None:
    outcomes, _ = python_outcomes[probe.family]
    got = outcomes.get(probe.name)
    assert got is not None, f"{probe.name}: no outcome (driver died?)"
    assert got["ok"], (
        f"{probe.name}: trapped with {got.get('kind')}: {got.get('message')}"
    )
    assert got["stdout"] == probe.expect


_NODE = shutil.which("node")


def _node_ready() -> bool:
    if _NODE is None:
        return False
    try:
        proc = subprocess.run(
            [_NODE, "--experimental-wasm-exnref", "-e", "0"],
            capture_output=True, timeout=10, check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return proc.returncode == 0


@pytest.mark.skipif(not _node_ready(), reason="Node.js with exnref unavailable")
@pytest.mark.parametrize(
    "probe", [p for p in PROBES if p.parity != "none"], ids=lambda p: p.name,
)
def test_probe_parity_on_browser_host(
    probe: Probe,
    python_outcomes: dict[str, tuple[dict[str, dict[str, object]], Path]],
) -> None:
    _, wasm = python_outcomes[probe.family]
    proc = subprocess.run(
        [_NODE or "node", "--experimental-wasm-exnref", "--stack-size=984",
         str(HARNESS), str(wasm), "--fn", probe.name],
        capture_output=True, text=True, encoding="utf-8", timeout=300,
        check=False, env=_child_env(),
    )
    assert proc.returncode == 0, proc.stderr[-2000:]
    out = json.loads(proc.stdout)
    assert out.get("error") is None, f"{probe.name}: {out.get('error')}"
    browser = str(out["stdout"])
    if probe.parity == "exact":
        assert browser == probe.expect
    else:
        assert browser.startswith(("Ok", "Err")), browser
