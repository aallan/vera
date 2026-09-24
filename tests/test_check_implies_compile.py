"""A program `vera check` accepts is a program code generation builds.

The class (#1489, #1493, #1506, #1509, #1233, and the family behind #1383):
the front end accepts a program that code generation then refuses or
silently drops.  Two mechanisms are closed here, and the instrument holds
three more shapes of the class.

* **An unresolved name** (#1489).  The checker's last-resort branch turned any
  type name nothing declares into an opaque type, and any effect name in a
  row into an effect instance, and reported nothing.  Code generation had no
  layout for the name and skipped the function (E602 / E603 / E604 / E605) —
  or, for a qualified effect reference, dropped it without a word.
* **A module registered without its own imports** (#1493).  Code generation
  measured each imported module's signatures in a namespace that held none
  of the module's imports, so a data type the module imported and returned
  had "no WASM representation", and a direct ``match`` on the call — in the
  importer or in the module's own bodies — dropped the enclosing function.

THE INSTRUMENT is one differential, run over three inputs: every program the
checker accepts compiles with no E6xx diagnostic, and every public function
of the entry file is exported (a drop that reports nothing is still a drop).

(a) :class:`TestUnresolvedNameMatrix` — an unresolved name in every grammar
    position that carries a type or effect name.  The positions are
    ENUMERATED from ``vera/grammar.lark`` (:func:`grammar_name_positions`),
    not listed: a rule that gains a type position fails the coverage cell
    until a cell exercises it.  Each cell carries a CONTROL — the same
    program with a declared name in that position — which must check,
    compile and export cleanly, so the refusal is caused by the name and
    nothing else in the template.
(b) :class:`TestModuleEnvironmentMatrix` — module topologies (a module
    returns a data type it imported; a third module consumes it; the module
    consumes it in its own body; a diamond) × every expression position the
    result can reach.  Expression positions are enumerated from the grammar
    too, plus the one the grammar cannot expose (a string interpolation
    segment, lexed inside ``STRING_LIT``), found by enumerating the AST's
    expression-bearing fields.
(c) :class:`TestCorpusCheckImpliesCompile` — every program under
    ``examples/``, ``tests/conformance/`` and ``tests/probes/``.  The
    programs that are check-green and still refused by code generation for
    a reason outside this class are held in an exact roster, each with the
    reason; a new one fails, and so does a stale entry.
(d) :class:`TestClauseOperationMatrix` — a handler-clause State operation
    code generation cannot lower is refused at check (E339, #1233), and the
    check-time walk must agree with code generation's own gate in both
    directions: handler nesting shapes × clause-body positions.
(e) :class:`TestNestedGenericCalls` — a generic call nested inside another
    compiles wherever it is written (#1509): every prelude generic as the
    outer call around every producer of its argument, in a function, a
    generic function and a ``where`` helper, in the entry file and in a
    module, each run to its value and held against the verifier's discovery
    (#732).

:class:`TestQuantifierShapes` (#1506) puts every type shape at a
quantifier's two type positions.
"""

from __future__ import annotations

import dataclasses
import itertools
import re
import typing
from dataclasses import dataclass
from pathlib import Path

import pytest
import wasmtime
from lark import Tree
from lark.grammar import NonTerminal
from lark.load_grammar import GrammarBuilder

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.errors import Diagnostic
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.runtime.traps import WasmTrapError
from vera.skip import STATE_CLAUSE_INLINE_DEPTH_CAP

_ROOT = Path(__file__).resolve().parent.parent
_GRAMMAR = _ROOT / "vera" / "grammar.lark"


# =====================================================================
# The harness: one pipeline, the one `vera run` uses
# =====================================================================

@dataclass
class Outcome:
    """What the toolchain did with one program."""

    #: Resolver and checker errors (warnings are not refusals).
    check_errors: list[Diagnostic]
    #: The compile result, or ``None`` when the checker refused.
    result: CompileResult | None
    #: What code generation refused: every E6xx diagnostic at any severity,
    #: and every error-severity diagnostic whatever its code (the guard
    #: rail's "is not defined" error carries none).
    drops: list[Diagnostic]
    #: Public, non-generic entry functions missing from the exports — a
    #: drop that reported nothing (a qualified effect row did exactly that).
    missing_exports: list[str]

    @property
    def accepted(self) -> bool:
        return not self.check_errors

    @property
    def compiles_clean(self) -> bool:
        return (self.result is not None and not self.drops
                and not self.missing_exports)

    @property
    def signature(self) -> tuple[str, ...]:
        """The refusal, as sorted codes (``"uncoded"`` for a codeless one)."""
        codes = [d.error_code or "uncoded" for d in self.drops]
        codes += ["missing-export"] * len(self.missing_exports)
        return tuple(sorted(codes))

    def describe(self) -> str:
        return (
            f"check_errors={[(d.error_code, d.description) for d in self.check_errors]} "
            f"drops={[(d.error_code, d.description) for d in self.drops]} "
            f"missing_exports={self.missing_exports}"
        )


def build(
    main_path: Path, source: str, root: Path, *, past_check: bool = False,
) -> Outcome:
    """Resolve, check and (if accepted) compile, as ``vera run`` does.

    *past_check* compiles a refused program too, so a refusal at check can
    be compared with what code generation would have done (the #1233
    differential): the check errors are still reported.
    """
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=root)
    resolved = resolver.resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    errors = list(resolver.errors) + [
        d for d in diags if d.severity == "error"
    ]
    if errors and not past_check:
        return Outcome(errors, None, [], [])
    result = codegen_compile(
        program, source=source, file=str(main_path),
        resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    drops = [
        d for d in result.diagnostics
        if (d.error_code or "").startswith("E6") or d.severity == "error"
    ]
    public = [
        tld.decl.name for tld in program.declarations
        if isinstance(tld.decl, ast.FnDecl)
        and tld.visibility == "public" and not tld.decl.forall_vars
    ]
    missing = [name for name in public if name not in result.exports]
    return Outcome(errors, result, drops, missing)


def pipeline(
    tmp_path: Path, files: dict[str, str], main: str = "main.vera",
    *, past_check: bool = False,
) -> Outcome:
    """Write *files* into *tmp_path* and :func:`build` *main*."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    return build(tmp_path / main, files[main], tmp_path,
                 past_check=past_check)


def run_main(outcome: Outcome) -> tuple[str, object]:
    """``("ok", value)`` or ``("trap", message)`` for ``main``."""
    assert outcome.result is not None
    try:
        return "ok", execute(outcome.result, fn_name="main").value
    except (WasmTrapError, wasmtime.WasmtimeError, wasmtime.Trap) as exc:
        return "trap", str(exc)


def locate(source: str, marker: str, occurrence: int = 0) -> tuple[int, int]:
    """1-based (line, column) of *marker*'s *occurrence*-th match in *source*."""
    idx = -1
    for _ in range(occurrence + 1):
        idx = source.index(marker, idx + 1)
    line = source.count("\n", 0, idx) + 1
    col = idx - (source.rfind("\n", 0, idx) + 1) + 1
    return line, col


# =====================================================================
# Enumerating positions from the grammar
# =====================================================================

def _grammar_alternatives() -> dict[str, list[tuple[str, frozenset[str]]]]:
    """Every rule's alternatives: ``(label, nonterminals it references)``.

    Read from the grammar's own definitions (pre-compilation, so a helper
    rule Lark synthesises for a ``*`` group is not mistaken for a position).
    An aliased alternative (``-> named_type``) is labelled by its alias; an
    unaliased one by its rule.
    """
    builder = GrammarBuilder()
    builder.load_grammar(_GRAMMAR.read_text(encoding="utf-8"), "<vera>")

    def refs(node: object, out: set[str]) -> None:
        if isinstance(node, Tree):
            for child in node.children:
                refs(child, out)
        elif isinstance(node, NonTerminal):
            out.add(node.name)

    table: dict[str, list[tuple[str, frozenset[str]]]] = {}
    for name, definition in builder._definitions.items():
        if definition.is_term:
            continue
        alternatives: list[tuple[str, frozenset[str]]] = []
        for alt in definition.tree.children:
            found: set[str] = set()
            if isinstance(alt, Tree) and alt.data == "alias":
                expansion, alias = alt.children
                refs(expansion, found)
                alternatives.append((alias.name, frozenset(found)))
            else:
                refs(alt, found)
                alternatives.append((str(name), frozenset(found)))
        table[str(name)] = alternatives
    return table


#: The nonterminals that carry a type NAME or an effect NAME.
NAME_CARRIERS = frozenset({"type_expr", "type_args", "effect_ref",
                           "effect_clause"})

#: The nonterminals that carry an expression.
EXPR_CARRIERS = frozenset({"expr", "arg_list", "block_expr", "block_contents",
                           "handler_body", "implies_expr", "or_expr",
                           "and_expr", "eq_expr", "cmp_expr", "add_expr",
                           "mul_expr", "unary_expr", "postfix_expr"})

#: The precedence ladder: an alternative that only forwards to the next rung
#: holds no position of its own.
_PASSTHROUGH = frozenset({"expr", "pipe_expr", "implies_expr", "or_expr",
                          "and_expr", "eq_expr", "cmp_expr", "add_expr",
                          "mul_expr", "unary_expr", "postfix_expr",
                          "primary_expr", "block_expr", "fn_body",
                          "arg_list", "handler_body"})


def _parents(
    table: dict[str, list[tuple[str, frozenset[str]]]],
) -> dict[str, set[str]]:
    parents: dict[str, set[str]] = {}
    for alternatives in table.values():
        for label, found in alternatives:
            for name in found:
                parents.setdefault(name, set()).add(label)
    return parents


def grammar_name_positions() -> frozenset[tuple[str, str, str]]:
    """Every grammar position that carries a type or effect name.

    A key is ``(alternative, carrier, parent)``: an alternative that
    references a :data:`NAME_CARRIERS` nonterminal, and each alternative
    that uses the alternative's rule — the syntactic context.  The three
    alternatives of ``type_expr`` (a named type, a function type, a
    refinement) stand everywhere a type does, so their context is ``"*"``:
    every other position is already a key.
    """
    table = _grammar_alternatives()
    parents = _parents(table)
    keys: set[tuple[str, str, str]] = set()
    for rule, alternatives in table.items():
        for label, found in alternatives:
            for carrier in found & NAME_CARRIERS:
                if rule == "type_expr":
                    keys.add((label, carrier, "*"))
                    continue
                for parent in parents.get(rule, set()):
                    # `fn_type` and `refinement_type` are alternatives of
                    # `type_expr`, so their context is every type position.
                    keys.add((label, carrier,
                              "*" if parent == "type_expr" else parent))
    return frozenset(keys)


def grammar_expression_positions() -> frozenset[str]:
    """Every grammar alternative that holds an expression position.

    The precedence ladder's pass-through alternatives (``?or_expr:
    and_expr``) are not positions; the operators on it are.
    """
    table = _grammar_alternatives()
    out: set[str] = set()
    for alternatives in table.values():
        for label, found in alternatives:
            if not found & EXPR_CARRIERS:
                continue
            if label in _PASSTHROUGH:
                continue
            out.add(label)
    return frozenset(out)


def ast_expression_fields() -> frozenset[tuple[str, str]]:
    """Every ``(node class, field)`` in :mod:`vera.ast` that holds an Expr.

    The grammar cannot see a string interpolation segment — it is lexed
    inside ``STRING_LIT`` and split by the transformer — so the AST is the
    second source, and the one that names that position.
    """
    out: set[tuple[str, str]] = set()
    for name, cls in vars(ast).items():
        if not (isinstance(cls, type) and dataclasses.is_dataclass(cls)):
            continue
        hints = typing.get_type_hints(cls, vars(ast))
        for f in dataclasses.fields(cls):
            if _holds_expr(hints.get(f.name)):
                out.add((name, f.name))
    return frozenset(out)


def _holds_expr(hint: object) -> bool:
    if isinstance(hint, type):
        return issubclass(hint, ast.Expr)
    return any(_holds_expr(arg) for arg in typing.get_args(hint))


# =====================================================================
# (a) Unresolved names in every type and effect position
# =====================================================================

#: The unresolved type name.  Nothing in the language, the prelude or any
#: template declares it, so no fallback can coincide with it.
TYPE_NAME = "Qzt"
#: The unresolved effect name, and a qualified reference — which names
#: nothing at all, since no effect declaration takes a qualified name.
EFFECT_NAME = "Qze"
QUALIFIED_EFFECT = "Qm.Qze"

_COLOUR = """\
private data Colour {
  Red,
  Green
}

"""

_MAIN0 = """

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""


@dataclass(frozen=True)
class NameCell:
    """One unresolved name at one grammar position, beside its control."""

    label: str
    #: The grammar keys (:func:`grammar_name_positions`) this cell exercises.
    positions: frozenset[tuple[str, str, str]]
    #: The program, with ``{N}`` where the name goes.
    template: str
    #: The unresolved spelling, and the declared spelling of the control.
    name: str
    control: str
    #: ``(code, marker, occurrence)`` diagnostics the variant must draw,
    #: each located at that occurrence of *marker* in the variant source.
    expect: tuple[tuple[str, str, int], ...]

    def variant_source(self) -> str:
        return self.template.replace("{N}", self.name)

    def control_source(self) -> str:
        return self.template.replace("{N}", self.control)


def _p(*keys: tuple[str, str, str]) -> frozenset[tuple[str, str, str]]:
    return frozenset(keys)


def _fn(sig: str, body: str, *, effects: str = "effects(pure)",
        contracts: str = "requires(true)\n  ensures(true)",
        where: str = "", forall: str = "") -> str:
    return (
        f"public {forall}fn f{sig}\n  {contracts}\n  {effects}\n"
        f"{{\n  {body}\n}}{where}\n"
    )


_T = TYPE_NAME
_E = EFFECT_NAME
_Q = QUALIFIED_EFFECT

UNRESOLVED_NAME_CELLS: tuple[NameCell, ...] = (
    # --- function signatures -------------------------------------------
    NameCell(
        "fn parameter",
        _p(("fn_params", "type_expr", "fn_signature"),
           ("named_type", "type_args", "*")),
        _COLOUR + _fn("(@{N} -> @Int)", "1") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "fn return",
        _p(("fn_signature", "type_expr", "fn_decl"),),
        _COLOUR + _fn("(@Int -> @Option<{N}>)", "None") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "type argument of a parameter",
        _p(("type_args", "type_expr", "named_type"),),
        _COLOUR + _fn("(@Option<{N}> -> @Int)", "1") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "refinement base",
        _p(("refinement_type", "type_expr", "*"),),
        _COLOUR + _fn("(@Array<{ @{N} | true }> -> @Int)", "1") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "function-type parameter",
        _p(("param_types", "type_expr", "fn_type"),
           ("fn_type", "type_expr", "*")),
        _COLOUR + _fn("(@Array<fn({N} -> Int) effects(pure)> -> @Int)", "1")
        + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "function-type result",
        _p(("fn_type", "type_expr", "*"),),
        _COLOUR + _fn("(@Array<fn(Int -> {N}) effects(pure)> -> @Int)", "1")
        + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    # --- declarations --------------------------------------------------
    NameCell(
        "constructor field",
        _p(("fields_constructor", "type_expr", "constructor_list"),),
        _COLOUR + "private data Box {\n  MkBox({N}),\n  Empty\n}\n" + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "type alias body",
        _p(("type_alias_decl", "type_expr", "top_level_decl"),),
        _COLOUR + "type Hue = Option<{N}>;\n" + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "effect operation parameter",
        _p(("param_types", "type_expr", "op_decl"),
           ("op_decl", "type_expr", "effect_decl")),
        _COLOUR + "effect Paint {\n  op daub({N} -> Unit);\n}\n" + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "effect operation result",
        _p(("op_decl", "type_expr", "effect_decl"),),
        _COLOUR + "effect Paint {\n  op pick(Unit -> {N});\n}\n" + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "ability operation result",
        _p(("op_decl", "type_expr", "ability_decl"),),
        _COLOUR + "ability Tint<A> {\n  op tint(A -> {N});\n}\n" + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "ability operation parameter",
        _p(("param_types", "type_expr", "op_decl"),
           ("op_decl", "type_expr", "ability_decl")),
        _COLOUR + "ability Tint<A> {\n  op tint(A, {N} -> Int);\n}\n"
        + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    # --- effect rows ---------------------------------------------------
    NameCell(
        "effect row of a function",
        _p(("fn_decl", "effect_clause", "fn_top_level"),
           ("effect_list", "effect_ref", "effect_set")),
        _fn("(@Int -> @Int)", "@Int.0", effects="effects(<{N}>)") + _MAIN0,
        _E, "IO", (("E338", _E, 0),),
    ),
    NameCell(
        "qualified effect in a function's row",
        _p(("fn_decl", "effect_clause", "fn_top_level"),
           ("effect_list", "effect_ref", "effect_set")),
        _fn("(@Int -> @Int)", "@Int.0", effects="effects(<{N}>)") + _MAIN0,
        _Q, "IO", (("E338", _Q, 0),),
    ),
    NameCell(
        "effect row of a where-helper",
        _p(("fn_decl", "effect_clause", "where_block"),),
        _fn("(@Int -> @Int)", "helper(@Int.0)", where=(
            "\nwhere {\n  fn helper(@Int -> @Int)\n    requires(true)\n"
            "    ensures(true)\n    effects(<{N}>)\n  {\n    @Int.0\n  }\n}"
        ), effects="effects(<IO>)") + _MAIN0,
        _E, "IO", (("E338", _E, 0),),
    ),
    NameCell(
        "effect row of a function type",
        _p(("fn_type", "effect_clause", "*"),),
        _fn("(@Array<fn(Int -> Int) effects(<{N}>)> -> @Int)", "1") + _MAIN0,
        _E, "IO", (("E338", _E, 0),),
    ),
    NameCell(
        "type argument of an effect in a row",
        _p(("effect_ref", "type_args", "effect_list"),
           ("type_args", "type_expr", "effect_ref")),
        _COLOUR + _fn("(@Int -> @Int)", "@Int.0",
                      effects="effects(<Exn<{N}>>)") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "type argument of a qualified effect in a row",
        _p(("qualified_effect_ref", "type_args", "effect_list"),
           ("type_args", "type_expr", "qualified_effect_ref")),
        _COLOUR + _fn("(@Int -> @Int)", "@Int.0",
                      effects="effects(<{N}>)") + _MAIN0,
        f"Qm.Qze<{_T}>", "Exn<Colour>", (("E338", "Qm.Qze", 0), ("E136", _T, 0)),
    ),
    # --- expressions that name a type ----------------------------------
    NameCell(
        "slot reference type argument",
        _p(("slot_ref", "type_args", "primary_expr"),
           ("type_args", "type_expr", "slot_ref")),
        _COLOUR + _fn("(@Option<Colour> -> @Int)",
                      "match @Option<{N}>.0 {\n    None -> 1,\n"
                      "    Some(@Colour) -> 2\n  }") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "result reference type argument",
        _p(("result_ref", "type_args", "primary_expr"),
           ("type_args", "type_expr", "result_ref")),
        _COLOUR + _fn(
            "(@Int -> @Option<Colour>)", "None",
            contracts="requires(true)\n  ensures(@Option<{N}>.result == None)",
        ) + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "let binding",
        _p(("let_stmt", "type_expr", "statement"),),
        _COLOUR + _fn("(@Int -> @Int)",
                      "let @Option<{N}> = None;\n  @Int.0") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "tuple destructure component",
        _p(("tuple_destruct", "type_expr", "let_destruct"),),
        _COLOUR + _fn(
            "(@Int -> @Int)",
            "let Tuple<@Int, @Option<{N}>> = Tuple(@Int.0, None);\n  @Int.0",
        ) + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "match binder",
        _p(("binding_pattern", "type_expr", "match_arm"),),
        _COLOUR + _fn("(@Int -> @Int)",
                      "match @Int.0 {\n    @{N} -> 1\n  }") + _MAIN0,
        _T, "Int", (("E136", _T, 0),),
    ),
    NameCell(
        "nested match binder",
        _p(("binding_pattern", "type_expr", "constructor_pattern"),),
        _COLOUR + _fn("(@Option<Colour> -> @Int)",
                      "match @Option<Colour>.0 {\n    None -> 1,\n"
                      "    Some(@{N}) -> 2\n  }") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "anonymous function parameter",
        _p(("fn_params", "type_expr", "anonymous_fn"),),
        _COLOUR + _fn("(@Array<Int> -> @Int)",
                      "array_length(array_map(array_map(@Array<Int>.0, "
                      "fn(@Int -> @Option<Colour>) effects(pure) { None }), "
                      "fn(@Option<{N}> -> @Int) effects(pure) { 1 }))")
        + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "anonymous function result",
        _p(("anonymous_fn", "type_expr", "primary_expr"),),
        _COLOUR + _fn("(@Array<Int> -> @Int)",
                      "array_length(array_map(@Array<Int>.0, "
                      "fn(@Int -> @Option<{N}>) effects(pure) { None }))")
        + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "anonymous function effect row",
        _p(("anonymous_fn", "effect_clause", "primary_expr"),),
        _fn("(@Array<Int> -> @Int)",
            "array_length(array_map(@Array<Int>.0, "
            "fn(@Int -> @Int) effects({N}) { @Int.0 }))") + _MAIN0,
        f"<{_E}>", "pure", (("E338", _E, 0),),
    ),
    NameCell(
        "forall quantifier binder",
        _p(("forall_expr", "type_expr", "primary_expr"),),
        _fn("(@Array<Int> -> @Int)", "1", contracts=(
            "requires(forall(@{N}, array_length(@Array<Int>.0), "
            "fn(@Nat -> @Bool) effects(pure) { true }))\n  ensures(true)"
        )) + _MAIN0,
        _T, "Nat", (("E136", _T, 0),),
    ),
    NameCell(
        "exists quantifier binder",
        _p(("exists_expr", "type_expr", "primary_expr"),),
        _fn("(@Array<Int> -> @Int)", "1", contracts=(
            "requires(true)\n  ensures(exists(@{N}, "
            "array_length(@Array<Int>.0), "
            "fn(@Nat -> @Bool) effects(pure) { true }) || true)"
        )) + _MAIN0,
        _T, "Nat", (("E136", _T, 0),),
    ),
    NameCell(
        "forall predicate parameter",
        _p(("anonymous_fn", "type_expr", "forall_expr"),),
        _fn("(@Array<Int> -> @Int)", "1", contracts=(
            "requires(forall(@Nat, array_length(@Array<Int>.0), "
            "fn(@{N} -> @Bool) effects(pure) { true }))\n  ensures(true)"
        )) + _MAIN0,
        _T, "Nat", (("E136", _T, 0),),
    ),
    NameCell(
        "forall predicate effect row",
        _p(("anonymous_fn", "effect_clause", "forall_expr"),),
        _fn("(@Array<Int> -> @Int)", "1", contracts=(
            "requires(forall(@Nat, array_length(@Array<Int>.0), "
            "fn(@Nat -> @Bool) effects({N}) { true }))\n  ensures(true)"
        )) + _MAIN0,
        f"<{_E}>", "pure", (("E338", _E, 0),),
    ),
    NameCell(
        "exists predicate parameter",
        _p(("anonymous_fn", "type_expr", "exists_expr"),),
        _fn("(@Array<Int> -> @Int)", "1", contracts=(
            "requires(true)\n  ensures(exists(@Nat, "
            "array_length(@Array<Int>.0), fn(@{N} -> @Bool) effects(pure) "
            "{ true }) || true)"
        )) + _MAIN0,
        _T, "Nat", (("E136", _T, 0),),
    ),
    NameCell(
        "exists predicate effect row",
        _p(("anonymous_fn", "effect_clause", "exists_expr"),),
        _fn("(@Array<Int> -> @Int)", "1", contracts=(
            "requires(true)\n  ensures(exists(@Nat, "
            "array_length(@Array<Int>.0), fn(@Nat -> @Bool) "
            "effects({N}) { true }) || true)"
        )) + _MAIN0,
        f"<{_E}>", "pure", (("E338", _E, 0),),
    ),
    # --- handlers and state forms --------------------------------------
    NameCell(
        "handled effect",
        _p(("handle_expr", "effect_ref", "primary_expr"),),
        _fn("(@Int -> @Int)",
            "handle[{N}](@Int = 0) {\n    get(@Unit) -> { resume(@Int.0) },\n"
            "    put(@Int) -> { resume(()) }\n  } in {\n    @Int.0\n  }")
        + _MAIN0,
        _E, "State<Int>", (("E330", _E, 0),),
    ),
    NameCell(
        "qualified handled effect",
        _p(("handle_expr", "effect_ref", "primary_expr"),),
        _fn("(@Int -> @Int)",
            "handle[{N}](@Int = 0) {\n    get(@Unit) -> { resume(@Int.0) },\n"
            "    put(@Int) -> { resume(()) }\n  } in {\n    @Int.0\n  }")
        + _MAIN0,
        _Q, "State<Int>", (("E330", _Q, 0),),
    ),
    NameCell(
        "type argument of a handled effect",
        _p(("effect_ref", "type_args", "handle_expr"),),
        _COLOUR + _fn("(@Int -> @Int)",
                      "handle[Exn<{N}>] {\n    throw(@Colour) -> 7\n  } in {\n"
                      "    @Int.0\n  }") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "type argument of a qualified handled effect",
        _p(("qualified_effect_ref", "type_args", "handle_expr"),),
        _COLOUR + _fn("(@Int -> @Int)",
                      "handle[{N}] {\n    throw(@Colour) -> 7\n  } in {\n"
                      "    @Int.0\n  }") + _MAIN0,
        f"Qm.Qze<{_T}>", "Exn<Colour>", (("E136", _T, 0),),
    ),
    NameCell(
        "handler state",
        _p(("handler_state", "type_expr", "handle_expr"),),
        _COLOUR + _fn("(@Int -> @Int)",
                      "handle[State<Int>](@{N} = 0) {\n"
                      "    get(@Unit) -> { resume(0) },\n"
                      "    put(@Int) -> { resume(()) }\n  } in {\n    @Int.0\n  }")
        + _MAIN0,
        _T, "Int", (("E136", _T, 0),),
    ),
    NameCell(
        "handler clause parameter",
        _p(("handler_params", "type_expr", "handler_clause"),),
        _COLOUR + _fn("(@Int -> @Int)",
                      "handle[Exn<Colour>] {\n    throw(@{N}) -> 7\n  } in {\n"
                      "    @Int.0\n  }") + _MAIN0,
        _T, "Colour", (("E136", _T, 0),),
    ),
    NameCell(
        "handler with-clause",
        _p(("with_clause", "type_expr", "handler_clause"),),
        _fn("(@Int -> @Int)",
            "handle[State<Int>](@Int = 0) {\n"
            "    get(@Unit) -> { resume(@Int.0) },\n"
            "    put(@Int) -> { resume(()) } with @{N} = @Int.0\n"
            "  } in {\n    @Int.0\n  }") + _MAIN0,
        _T, "Int", (("E136", _T, 0),),
    ),
    NameCell(
        "old() effect",
        _p(("old_expr", "effect_ref", "primary_expr"),),
        _fn("(@Int -> @Unit)", "put(@Int.0);\n  ()",
            effects="effects(<State<Int>>)",
            contracts="requires(true)\n  ensures(old({N}) == old({N}))")
        + _MAIN0,
        _E, "State<Int>", (("E177", "old(", 0),),
    ),
    NameCell(
        "new() effect",
        _p(("new_expr", "effect_ref", "primary_expr"),),
        _fn("(@Int -> @Unit)", "put(@Int.0);\n  ()",
            effects="effects(<State<Int>>)",
            contracts="requires(true)\n  ensures(new({N}) == new({N}))")
        + _MAIN0,
        _E, "State<Int>", (("E177", "new(", 0),),
    ),
    NameCell(
        "type argument of an old() effect",
        _p(("effect_ref", "type_args", "old_expr"),),
        _fn(
            "(@Int -> @Unit)", "put(@Int.0);\n  ()",
            effects="effects(<State<{N}>>)",
            contracts="requires(true)\n  ensures(old(State<{N}>) "
                      "== old(State<{N}>))",
        ) + _MAIN0,
        _T, "Int", (("E136", _T, 0),),
    ),
    NameCell(
        "type argument of a new() effect",
        _p(("effect_ref", "type_args", "new_expr"),),
        _fn(
            "(@Int -> @Unit)", "put(@Int.0);\n  ()",
            effects="effects(<State<{N}>>)",
            contracts="requires(true)\n  ensures(new(State<{N}>) "
                      "== new(State<{N}>))",
        ) + _MAIN0,
        _T, "Int", (("E136", _T, 0),),
    ),
    NameCell(
        "type argument of a qualified old() effect",
        _p(("qualified_effect_ref", "type_args", "old_expr"),),
        _fn("(@Int -> @Unit)", "put(@Int.0);\n  ()",
            effects="effects(<State<Int>>)",
            contracts="requires(true)\n  ensures(old({N}) == old({N}))")
        + _MAIN0,
        f"Qm.Qze<{_T}>", "State<Int>", (("E136", _T, 0),),
    ),
    NameCell(
        "type argument of a qualified new() effect",
        _p(("qualified_effect_ref", "type_args", "new_expr"),),
        _fn("(@Int -> @Unit)", "put(@Int.0);\n  ()",
            effects="effects(<State<Int>>)",
            contracts="requires(true)\n  ensures(new({N}) == new({N}))")
        + _MAIN0,
        f"Qm.Qze<{_T}>", "State<Int>", (("E136", _T, 0),),
    ),
)


def _single_file_outcome(tmp_path: Path, source: str) -> Outcome:
    return pipeline(tmp_path, {"main.vera": source})


class TestUnresolvedNameMatrix:
    """(a): an unresolved name in every grammar position that holds one."""

    def test_every_grammar_position_has_a_cell(self) -> None:
        """The positions come from the grammar; every one needs a cell.

        A grammar change that adds a type or effect position fails here
        until a cell puts an unresolved name there — which is the point of
        enumerating rather than listing.  A cell that claims a position the
        grammar does not have fails too, so the claims cannot rot.
        """
        wanted = grammar_name_positions()
        claimed = frozenset().union(
            *(cell.positions for cell in UNRESOLVED_NAME_CELLS))
        assert not wanted - claimed, sorted(wanted - claimed)
        assert not claimed - wanted, sorted(claimed - wanted)

    def test_the_enumeration_sees_the_positions_the_issue_names(self) -> None:
        """The enumerator is not vacuous: it finds the reported shapes."""
        wanted = grammar_name_positions()
        for key in (
            ("fn_params", "type_expr", "fn_signature"),      # f(@Nonexistent)
            ("type_args", "type_expr", "named_type"),        # Option<Nonexistent>
            ("binding_pattern", "type_expr", "constructor_pattern"),
            ("fields_constructor", "type_expr", "constructor_list"),
            ("let_stmt", "type_expr", "statement"),          # let @Colour
            ("fn_decl", "effect_clause", "fn_top_level"),    # effects(<X>)
        ):
            assert key in wanted, key
        assert len(wanted) >= 40, len(wanted)

    @pytest.mark.parametrize(
        "cell", UNRESOLVED_NAME_CELLS, ids=lambda c: c.label,
    )
    def test_control_checks_compiles_and_exports(
        self, cell: NameCell, tmp_path: Path,
    ) -> None:
        """The template is sound with a declared name in the position.

        So the variant's refusal below is caused by the name and nothing
        else — and the differential holds on the accepted program.
        """
        outcome = _single_file_outcome(tmp_path, cell.control_source())
        assert outcome.accepted, outcome.describe()
        assert outcome.compiles_clean, outcome.describe()

    @pytest.mark.parametrize(
        "cell", UNRESOLVED_NAME_CELLS, ids=lambda c: c.label,
    )
    def test_unresolved_name_is_refused_where_it_is_written(
        self, cell: NameCell, tmp_path: Path,
    ) -> None:
        """Every type and effect name resolves, or check refuses it there."""
        source = cell.variant_source()
        outcome = _single_file_outcome(tmp_path, source)
        # The differential, stated first: an accepted program compiles.
        if outcome.accepted:
            assert outcome.compiles_clean, outcome.describe()
        got = {
            (d.error_code, d.location.line, d.location.column)
            for d in outcome.check_errors
        }
        for code, marker, occurrence in cell.expect:
            line, col = locate(source, marker, occurrence)
            assert (code, line, col) in got, (
                f"expected {code} at {line}:{col} ({marker!r}); "
                + outcome.describe()
            )


#: Type SHAPES at the quantifier's two type positions (#1506): the index
#: type, and the predicate's parameter — the grammar keys
#: ``(forall_expr|exists_expr, type_expr, primary_expr)`` and
#: ``(anonymous_fn, type_expr, forall_expr|exists_expr)``.  The name matrix
#: above puts a declared NAME in each; a refinement, an alias of one, or a
#: type with no integer representation is a different shape.  At the
#: predicate's parameter each one used to pass check and verify and then stop
#: code generation (E699) or leave a module that fails to load; at the index
#: type a non-integer was accepted and ignored, and a refinement was ignored
#: by the runtime check that should range over it.
QUANTIFIER_SHAPES: tuple[tuple[str, int | None, bool], ...] = (
    # (spelling, the INDEX values it admits below 5 — None when it is not
    #  an index type — and whether the PREDICATE may take it)
    ("Nat", 5, True),
    ("Int", 5, True),
    ("Idx", 5, True),                           # an alias of Nat
    ("{ @Nat | @Nat.0 < 100 }", 5, False),      # an inline refinement
    ("Small", 2, False),                        # an alias of a refinement
    ("{ @Nat | @Nat.0 > 10 }", 0, False),       # a refinement none satisfy
    ("Byte", None, False),                      # an integer, not an index
    ("Bool", None, False),
    ("Option<Int>", None, False),
    ("Colour", None, False),
)

_QUANT_PRELUDE = (
    "private data Colour {\n  Red,\n  Green\n}\n\ntype Idx = Nat;\n"
    "type Small = { @Nat | @Nat.0 < 2 };\n\n"
)

#: Each quantifier's body over its index, and the answer over the first
#: ``n`` indices — a body whose value depends on the index, so a check that
#: ignored the index's refinement would give a different answer.
_QUANT_BODY = {
    "forall": ("{I}.0 < 3", lambda n: 1 if n <= 3 else 0),
    "exists": ("{I}.0 > 0", lambda n: 1 if n >= 2 else 0),
}


@dataclass(frozen=True)
class QuantifierCell:
    form: str
    position: str       # "binding" or "predicate"
    shape: str
    admits: int | None  # index values the shape admits below 5
    predicate_ok: bool

    @property
    def label(self) -> str:
        return f"{self.form}|{self.position}|{self.shape}"

    @property
    def refusal(self) -> str | None:
        """The code that refuses the cell, or None when it must run."""
        if self.position == "binding":
            return "E186" if self.admits is None else None
        return None if self.predicate_ok else "E179"

    @property
    def value(self) -> int:
        _body, answer = _QUANT_BODY[self.form]
        n = self.admits if self.position == "binding" else 5
        assert n is not None
        return answer(n)

    def source(self) -> str:
        binding = self.shape if self.position == "binding" else "Nat"
        param = self.shape if self.position == "predicate" else "Nat"
        body, _answer = _QUANT_BODY[self.form]
        if self.refusal is not None and self.position == "predicate":
            body_text = "true"
        else:
            body_text = body.replace("{I}", f"@{param}")
        return (
            _QUANT_PRELUDE + "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            f"  if {self.form}(@{binding}, 5, fn(@{param} -> @Bool) "
            f"effects(pure) {{ {body_text} }}) then {{ 1 }} else {{ 0 }}\n}}\n"
        )


QUANTIFIER_CELLS: tuple[QuantifierCell, ...] = tuple(
    QuantifierCell(form, position, shape, admits, predicate_ok)
    for form in ("forall", "exists")
    for position in ("binding", "predicate")
    for shape, admits, predicate_ok in QUANTIFIER_SHAPES
)

#: A type parameter at each of the quantifier's type positions, in a generic
#: instantiated at each of these types (#1506 review): refused where it is
#: written, whatever the instantiation.
_TYPE_PARAM_POSITIONS = {
    "index": ("E186", "forall(@T, 3, fn(@Nat -> @Bool) effects(pure) "
                      "{ true })"),
    "predicate parameter": ("E179", "forall(@Nat, 3, fn(@T -> @Bool) "
                                    "effects(pure) { true })"),
    "predicate result": ("E179", "forall(@Nat, 3, fn(@Nat -> @T) "
                                 "effects(pure) { @T.0 })"),
    "bound": ("E128", "forall(@Nat, @T.0, fn(@Nat -> @Bool) effects(pure) "
                      "{ true })"),
}

#: The instantiations that are written into a module that fails to load:
#: a type parameter defers to the instantiation (PR #1202), and nothing
#: checks it there yet.  Checking these where the types are known is
#: #1506's remaining work; each cell flips when it lands.
_TYPE_PARAM_GAPS = frozenset({
    ("predicate result", "Int"), ("predicate result", "Nat"),
    ("bound", "Bool"), ("bound", "String"), ("bound", "Colour"),
})
_TYPE_PARAM_ARGS = {
    "Bool": "true", "Int": "5", "Nat": "5", "String": '"abc"', "Colour": "Red",
}


@dataclass(frozen=True)
class TypeParamCell:
    position: str
    instance: str

    @property
    def label(self) -> str:
        return f"{self.position}|T={self.instance}"

    def source(self) -> str:
        _code, quant = _TYPE_PARAM_POSITIONS[self.position]
        return (
            _QUANT_PRELUDE
            + "private forall<T> fn q(@T -> @Bool)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            f"  {quant}\n}}\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            f"  if q({_TYPE_PARAM_ARGS[self.instance]}) then {{ 1 }} "
            "else { 0 }\n}\n"
        )


TYPE_PARAM_CELLS: tuple[TypeParamCell, ...] = tuple(
    TypeParamCell(position, instance)
    for position in _TYPE_PARAM_POSITIONS
    for instance in _TYPE_PARAM_ARGS
)

_TYPE_PARAM_PARAMS = [
    pytest.param(cell, id=cell.label, marks=pytest.mark.xfail(
        strict=True,
        reason="#1506: checked at the instantiation next, not yet"))
    if (cell.position, cell.instance) in _TYPE_PARAM_GAPS
    else pytest.param(cell, id=cell.label)
    for cell in TYPE_PARAM_CELLS
]


class TestQuantifierShapes:
    """(a), continued: every type shape at the quantifier's positions."""

    @pytest.mark.parametrize("cell", QUANTIFIER_CELLS, ids=lambda c: c.label)
    def test_accepted_means_compiled(
        self, cell: QuantifierCell, tmp_path: Path,
    ) -> None:
        outcome = _single_file_outcome(tmp_path, cell.source())
        if cell.refusal is not None:
            assert cell.refusal in {
                d.error_code for d in outcome.check_errors}, (
                outcome.describe())
            return
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        # The index's refinement is honoured: a body that depends on the
        # index answers over the values the index type admits.
        assert run_main(outcome) == ("ok", cell.value)

    @pytest.mark.parametrize("cell", _TYPE_PARAM_PARAMS)
    def test_a_type_parameter_defers_to_the_instantiation(
        self, cell: TypeParamCell, tmp_path: Path,
    ) -> None:
        """A quantifier position typed by a type parameter is accepted, as
        E128 accepts the bound's (PR #1202): the integer instantiations
        run.  The ones that cannot are the strict xfails above."""
        outcome = _single_file_outcome(tmp_path, cell.source())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 1)

    def test_the_refinement_changes_the_answer(self) -> None:
        """Not vacuous: at the index position, a refined shape's expected
        value differs from the unrefined one for both quantifiers."""
        for form in ("forall", "exists"):
            values = {
                c.shape: c.value for c in QUANTIFIER_CELLS
                if c.form == form and c.position == "binding"
                and c.refusal is None
            }
            assert len(set(values.values())) > 1, (form, values)


# =====================================================================
# (b) A module's imported data type, through every expression position
# =====================================================================

#: The value under test: a call into a module whose return type the module
#: IMPORTED.  ``pick(1)`` is ``Red``; ``paint(Red)`` is ``1``.
_X = "pick(@Int.0)"

_MB = """\
module mb;

public data Colour {
  Red,
  Green
}
"""

_PICK = """
public fn pick(@Int -> @Colour)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { Red } else { Green }
}
"""

_PAINT = """
public fn paint(@Colour -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Colour.0 {
    Red -> 1,
    Green -> 2
  }
}
"""

_MA = "module ma;\n\nimport mb(Colour);\n" + _PICK + _PAINT

_MAIN_CALLS_CONSUME = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  consume(1)
}
"""


def _consume(body: str, contracts: str) -> str:
    return (
        "\npublic fn consume(@Int -> @Int)\n"
        f"  {contracts}\n  effects(pure)\n{{\n  {body}\n}}\n"
    )


#: A module that declares a constructor named like one of `Colour`'s and is
#: imported for an unrelated function (#1535).  No namespace can name both
#: `Green`s, so the program is legal, and code generation qualifies `mb`'s
#: types apart (#1317): `Colour` is `mod$mb$Colour` in every namespace that
#: can name it.
_MH = """\
module mh;

public data Hue {
  Green,
  Blue
}

public fn blue(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  3
}
"""


@dataclass(frozen=True)
class Topology:
    """Where the module result is produced, and where it is consumed."""

    label: str
    #: The module that supplies ``paint`` for a module-qualified call.
    paint_module: str
    #: Whether a sibling module declares a constructor named like one of
    #: `Colour`'s, so the program's `Colour` is owner-qualified (#1535).
    contended: bool = False

    @property
    def name(self) -> str:
        return self.label + (", owner-qualified" if self.contended else "")

    def files(self, consumer: str) -> dict[str, str]:
        """The program, with *consumer* (declarations) placed in it."""
        files = self._files(consumer)
        if self.contended:
            files["mh.vera"] = _MH
            files["main.vera"] = "import mh(blue);\n" + files[
                "main.vera"].replace("  consume(1)\n", "  consume(1) + blue(()) - 3\n")
        return files

    def _files(self, consumer: str) -> dict[str, str]:
        if self.label == "entry consumes":
            # A imports B's type and returns it; the entry consumes it.
            return {
                "mb.vera": _MB, "ma.vera": _MA,
                "main.vera": "import ma(pick, paint);\nimport mb(Colour);\n"
                             + consumer + _MAIN_CALLS_CONSUME,
            }
        if self.label == "module consumes":
            # C imports A: a third module's body consumes it, compiled as
            # an import.
            return {
                "mb.vera": _MB, "ma.vera": _MA,
                "mc.vera": "module mc;\n\nimport ma(pick, paint);\n"
                           "import mb(Colour);\n" + consumer,
                "main.vera": "import mc(consume);\n" + _MAIN_CALLS_CONSUME,
            }
        if self.label == "own body consumes":
            # A's own body consumes its own result, compiled as an import.
            return {
                "mb.vera": _MB, "ma.vera": _MA + consumer,
                "main.vera": "import ma(consume);\n" + _MAIN_CALLS_CONSUME,
            }
        if self.label == "diamond":
            # Two modules import B; the entry imports both and B.  ``paint``
            # is declared by ``mc`` alone: a second module declaring it too
            # is #1498's shape (E608 between two modules no namespace can
            # name together), which is not this class.
            return {
                "mb.vera": _MB,
                "ma.vera": "module ma;\n\nimport mb(Colour);\n" + _PICK,
                "mc.vera": "module mc;\n\nimport mb(Colour);\n" + _PAINT,
                "main.vera": "import ma(pick);\nimport mc(paint);\n"
                             "import mb(Colour);\n"
                             + consumer + _MAIN_CALLS_CONSUME,
            }
        raise AssertionError(self.label)


TOPOLOGIES: tuple[Topology, ...] = (
    Topology("entry consumes", "ma"),
    Topology("module consumes", "ma"),
    Topology("own body consumes", "ma"),
    Topology("diamond", "mc"),
    # #1535: where the entry does not import `Colour`, the sibling's `Green`
    # qualifies `mb`'s types apart; where it does, the rename falls on the
    # sibling's `Hue` instead, and `Colour` keeps its name.
    Topology("module consumes", "ma", contended=True),
    Topology("own body consumes", "ma", contended=True),
)


@dataclass(frozen=True)
class FlowCell:
    """The module result in one expression position."""

    label: str
    #: Grammar alternatives (:func:`grammar_expression_positions`) and AST
    #: fields (:func:`ast_expression_fields`) the result sits in directly.
    grammar: frozenset[str]
    fields: frozenset[tuple[str, str]]
    #: ``consume``'s body, with ``{X}`` for the module result and
    #: ``{PAINT}`` for the module a qualified ``paint`` call names.
    body: str
    #: The value ``main`` returns, or the code the checker refuses the
    #: position with — the result's type does not fit it.  Stated either
    #: way, so a refused cell says WHY it is refused.
    expect: int | str
    #: Declarations placed beside ``consume``.
    extra: str = ""
    contracts: str = "requires(true)\n  ensures(true)"
    #: Per-topology overrides of *expect*.
    per_topology: tuple[tuple[str, int | str], ...] = ()

    def expected(self, topology: Topology) -> int | str:
        return dict(self.per_topology).get(topology.label, self.expect)

    def consumer(self, topology: Topology) -> str:
        def fill(text: str) -> str:
            return (text.replace("{X}", _X)
                    .replace("{PAINT}", topology.paint_module))
        return fill(self.extra) + _consume(fill(self.body),
                                           fill(self.contracts))


def _g(*names: str) -> frozenset[str]:
    return frozenset(names)


def _f(*fields: tuple[str, str]) -> frozenset[tuple[str, str]]:
    return frozenset(fields)


_PAIR = """
private data Pair {
  MkPair(Colour, Int)
}
"""

_RELAY = """
private fn relay(@Int -> @Colour)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(@Int.0)
}
"""

_STATE_CLAUSES = (
    "get(@Unit) -> { resume(@Colour.0) },\n"
    "    put(@Colour) -> { resume(()) }"
)

FLOW_CELLS: tuple[FlowCell, ...] = (
    FlowCell("match scrutinee", _g("match_expr"),
             _f(("MatchExpr", "scrutinee")),
             "match {X} {\n    Red -> 10,\n    Green -> 20\n  }", 10),
    FlowCell("match arm", _g("match_arm"), _f(("MatchArm", "body")),
             "paint(match @Int.0 {\n    0 -> Green,\n    @Int -> {X}\n  })", 1),
    FlowCell("call argument", _g("func_call"), _f(("FnCall", "args")),
             "paint({X})", 1),
    FlowCell("module-qualified call argument", _g("module_call"),
             _f(("ModuleCall", "args")), "{PAINT}::paint({X})", 1),
    FlowCell("constructor argument", _g("constructor_call"),
             _f(("ConstructorCall", "args")),
             "match Some({X}) {\n    Some(@Colour) -> paint(@Colour.0),\n"
             "    None -> 0\n  }", 1),
    FlowCell("user constructor field", _g("constructor_call"),
             _f(("ConstructorCall", "args")),
             "match MkPair({X}, 3) {\n"
             "    MkPair(@Colour, @Int) -> paint(@Colour.0) + @Int.0\n  }", 4,
             extra=_PAIR),
    FlowCell("tuple component", _g("constructor_call", "let_destruct"),
             _f(("ConstructorCall", "args"), ("LetDestruct", "value")),
             "let Tuple<@Colour, @Int> = Tuple({X}, 5);\n"
             "  paint(@Colour.0) + @Int.0", 6),
    FlowCell("let binding", _g("let_stmt"), _f(("LetStmt", "value")),
             "let @Colour = {X};\n  paint(@Colour.0)", 1),
    FlowCell("array element", _g("array_literal"),
             _f(("ArrayLit", "elements")),
             "let @Array<Colour> = [{X}, Green];\n  paint(@Array<Colour>.0[0])",
             1),
    FlowCell("function return", _g("block_contents"),
             _f(("Block", "expr"), ("FnDecl", "body")),
             "paint(relay(@Int.0))", 1, extra=_RELAY),
    FlowCell("block tail", _g("block_contents"), _f(("Block", "expr")),
             "paint({\n    {X}\n  })", 1),
    FlowCell("if branch", _g("if_expr"),
             _f(("IfExpr", "then_branch"), ("IfExpr", "else_branch")),
             "paint(if @Int.0 > 0 then { {X} } else { Green })", 1),
    FlowCell("if condition", _g("if_expr"), _f(("IfExpr", "condition")),
             "if {X} then { 1 } else { 2 }", "E300"),
    FlowCell("parenthesised", _g("paren_expr"), frozenset(),
             "paint(({X}))", 1),
    FlowCell("pipe", _g("pipe"), frozenset(), "{X} |> paint()", 1),
    FlowCell("equality", _g("eq_op"),
             _f(("BinaryExpr", "left"), ("BinaryExpr", "right")),
             "if {X} == Red then { 1 } else { 2 }", 1),
    FlowCell("inequality", _g("neq_op"),
             _f(("BinaryExpr", "left"), ("BinaryExpr", "right")),
             "if Green != {X} then { 1 } else { 2 }", 1),
    FlowCell("expression statement", _g("expr_stmt"),
             _f(("ExprStmt", "expr")), "{X};\n  paint({X})", 1),
    FlowCell("handler state", _g("handler_state", "qualified_call"),
             _f(("HandlerState", "init_expr"), ("QualifiedCall", "args")),
             "handle[State<Colour>](@Colour = {X}) {\n    "
             + _STATE_CLAUSES + "\n  } in {\n    State.put({X});\n"
             "    paint(State.get(()))\n  }", 1),
    FlowCell("handler with-clause", _g("with_clause"),
             _f(("HandlerClause", "state_update")),
             "handle[State<Colour>](@Colour = Green) {\n"
             "    get(@Unit) -> { resume(@Colour.0) },\n"
             "    put(@Colour) -> { resume(()) } with @Colour = {X}\n"
             "  } in {\n    put(Green);\n    paint(get(()))\n  }", 1),
    FlowCell("handler clause body", _g("handler_clause"),
             _f(("HandlerClause", "body")),
             "paint(handle[Exn<Int>] {\n    throw(@Int) -> {X}\n  } in {\n"
             "    if @Int.0 > 5 then { Green } else { throw(0) }\n  })", 2),
    FlowCell("handled body", _g("handle_expr"), _f(("HandleExpr", "body")),
             "paint(handle[State<Int>](@Int = 0) {\n"
             "    get(@Unit) -> { resume(@Int.0) },\n"
             "    put(@Int) -> { resume(()) }\n  } in {\n    {X}\n  })", 1),
    FlowCell("anonymous function body", frozenset(), _f(("AnonFn", "body")),
             "paint(array_map([@Int.0], "
             "fn(@Int -> @Colour) effects(pure) { pick(@Int.0) })[0])", 1),
    FlowCell("interpolation segment", frozenset(),
             _f(("InterpolatedString", "parts")),
             'string_length("\\({X})")', "E148"),
    FlowCell("interpolation of a result through a call", frozenset(),
             _f(("InterpolatedString", "parts")),
             'string_length("colour \\(paint({X}))")', 8),
    FlowCell("requires clause", _g("requires_clause"),
             _f(("Requires", "expr")), "1", "E123",
             contracts="requires({X})\n  ensures(true)"),
    FlowCell("ensures clause", _g("ensures_clause"),
             _f(("Ensures", "expr")), "1", "E124",
             contracts="requires(true)\n  ensures({X})"),
    FlowCell("a contract calling through the result",
             _g("func_call"), _f(("FnCall", "args")), "1", 1,
             contracts="requires(true)\n  ensures(paint({X}) >= 1)"),
    FlowCell("decreases clause", _g("decreases_clause"),
             _f(("Decreases", "exprs")), "1", 1,
             contracts="requires(true)\n  ensures(true)\n  decreases({X})"),
    FlowCell("assert", _g("assert_expr"), _f(("AssertExpr", "expr")),
             "assert({X});\n  1", "E172"),
    FlowCell("assume", _g("assume_expr"), _f(("AssumeExpr", "expr")),
             "assume({X});\n  1", "E173"),
    FlowCell("forall domain", _g("forall_expr"),
             _f(("ForallExpr", "domain"), ("ForallExpr", "predicate")),
             "1", "E128",
             contracts="requires(forall(@Nat, {X}, fn(@Nat -> @Bool) "
                       "effects(pure) { true }))\n  ensures(true)"),
    FlowCell("exists domain", _g("exists_expr"),
             _f(("ExistsExpr", "domain"), ("ExistsExpr", "predicate")),
             "1", "E128",
             contracts="requires(exists(@Nat, {X}, fn(@Nat -> @Bool) "
                       "effects(pure) { true }))\n  ensures(true)"),
    FlowCell("index collection", _g("index_op"),
             _f(("IndexExpr", "collection")), "{X}[0]", "E161"),
    FlowCell("index position", _g("index_op"), _f(("IndexExpr", "index")),
             "[1, 2][{X}]", "E160"),
    FlowCell("logical not", _g("not_op"), _f(("UnaryExpr", "operand")),
             "if !{X} then { 1 } else { 2 }", "E146"),
    FlowCell("negation", _g("neg_op"), _f(("UnaryExpr", "operand")),
             "-{X}", "E147"),
    FlowCell("implication", _g("implies"), frozenset(),
             "if {X} ==> true then { 1 } else { 2 }", "E144"),
    FlowCell("disjunction", _g("or_op"), frozenset(),
             "if {X} || true then { 1 } else { 2 }", "E144"),
    FlowCell("conjunction", _g("and_op"), frozenset(),
             "if {X} && true then { 1 } else { 2 }", "E144"),
    *(
        FlowCell(f"arithmetic {op}", _g(label), frozenset(),
                 f"{{X}} {op} 1", "E140")
        for label, op in (("add_op", "+"), ("sub_op", "-"), ("mul_op", "*"),
                          ("div_op", "/"), ("mod_op", "%"))
    ),
    *(
        FlowCell(f"ordering {op}", _g(label), frozenset(),
                 f"if {{X}} {op} Red then {{ 1 }} else {{ 2 }}", "E143")
        for label, op in (("lt_op", "<"), ("gt_op", ">"), ("le_op", "<="),
                          ("ge_op", ">="))
    ),
    FlowCell("data invariant", _g("invariant_clause"),
             _f(("DataDecl", "invariant"), ("Invariant", "expr")),
             "1", "E120",
             extra="\nprivate data Held invariant(pick(1)) {\n"
                   "  MkHeld(Int)\n}\n"),
    FlowCell("refinement predicate", _g("refinement_type"),
             _f(("RefinementType", "predicate")), "1", "E126",
             extra="\ntype Tagged = { @Int | pick(@Int.0) };\n"),
)


class TestModuleEnvironmentMatrix:
    """(b): a data type a module imported, through every position."""

    def test_every_expression_position_has_a_cell(self) -> None:
        """Grammar positions and AST fields both enumerate; both need cells.

        The grammar gives operator granularity (``eq_op`` vs ``add_op``);
        the AST gives the positions the grammar cannot show — a string
        interpolation segment is lexed inside ``STRING_LIT``.  A private
        AST helper (``_WithClause``, the transformer's sentinel) is not a
        node a program can hold.
        """
        grammar = grammar_expression_positions()
        claimed = frozenset().union(*(c.grammar for c in FLOW_CELLS))
        assert not grammar - claimed, sorted(grammar - claimed)
        assert not claimed - grammar, sorted(claimed - grammar)
        fields = {f for f in ast_expression_fields()
                  if not f[0].startswith("_")}
        claimed_fields = frozenset().union(*(c.fields for c in FLOW_CELLS))
        assert not fields - claimed_fields, sorted(fields - claimed_fields)
        assert not claimed_fields - fields, sorted(claimed_fields - fields)

    @pytest.mark.parametrize("topology", TOPOLOGIES, ids=lambda t: t.name)
    @pytest.mark.parametrize("cell", FLOW_CELLS, ids=lambda c: c.label)
    def test_accepted_means_compiled(
        self, cell: FlowCell, topology: Topology, tmp_path: Path,
        request: pytest.FixtureRequest,
    ) -> None:
        """Accepted: compiles clean and runs to the value.  Else: refused."""
        if (cell.label == "module-qualified call argument"
                and topology.label == "own body consumes"):
            # `ma::paint(...)` in `ma`'s own body: a module's call to itself,
            # qualified.  `main` and this branch's base run it; the release
            # branch refuses it at check (E230, "Module 'ma' not found"),
            # #1558, outside this class.  Strict, so the cell turns red when
            # that is fixed.
            request.node.add_marker(pytest.mark.xfail(
                strict=True,
                reason="#1558: a module's self-qualified call is E230"))
        outcome = pipeline(tmp_path, topology.files(cell.consumer(topology)))
        expected = cell.expected(topology)
        if isinstance(expected, str):
            codes = {d.error_code for d in outcome.check_errors}
            assert expected in codes, outcome.describe()
            return
        assert outcome.accepted, outcome.describe()
        assert outcome.compiles_clean, outcome.describe()
        assert run_main(outcome) == ("ok", expected)

    @pytest.mark.parametrize(
        "topology", [t for t in TOPOLOGIES if t.contended],
        ids=lambda t: t.name)
    def test_the_contended_topologies_are_owner_qualified(
        self, topology: Topology, tmp_path: Path,
    ) -> None:
        """Not vacuous: the sibling's `Green` renames `mb`'s types, so the
        module's `pick` returns `mod$mb$Colour`."""
        from vera.codegen.core import CodeGenerator

        cell = next(c for c in FLOW_CELLS if c.label == "call argument")
        files = topology.files(cell.consumer(topology))
        for name, text in files.items():
            (tmp_path / name).write_text(text, encoding="utf-8")
        program = parse_to_ast(files["main.vera"])
        resolved = ModuleResolver(_root=tmp_path).resolve_imports(
            program, tmp_path / "main.vera")
        gen = CodeGenerator(source=files["main.vera"],
                            file=str(tmp_path / "main.vera"),
                            resolved_modules=resolved)
        gen.compile_program(parse_to_ast(files["main.vera"]))
        assert "mod$mb$Colour" in gen._adt_layouts, sorted(gen._adt_layouts)

    def test_the_reported_program(self, tmp_path: Path) -> None:
        """#1535's program: `ma` imports `mb`'s `Colour` and returns it, and
        the entry imports `mc`, whose `Hue` also has a `Green`.  The release
        branch dropped `ma`'s `pick` (E605) and `main` behind it (E620);
        `main` (6dc41d40) refused the program with E610."""
        mb = "module mb;\n\npublic data Colour {\n  Red,\n  Green\n}\n"
        mc = _MH.replace("module mh;", "module mc;")
        ma = ("module ma;\n\nimport mb(Colour);\n\n"
              "public fn paint(@Colour -> @Int)\n" + _NC
              + "{\n  match @Colour.0 {\n    Red -> 1,\n    Green -> 2\n  }\n}\n\n"
              "public fn pick(@Int -> @Colour)\n" + _NC
              + "{\n  if @Int.0 == 0 then {\n    Red\n  } else {\n    Green\n"
              "  }\n}\n")
        main = ("import ma(paint, pick);\nimport mc(blue);\n\n"
                "public fn main(@Unit -> @Int)\n" + _NC
                + "{\n  paint(pick(1)) + blue(())\n}\n")
        outcome = pipeline(tmp_path, {"mb.vera": mb, "mc.vera": mc,
                                      "ma.vera": ma, "main.vera": main})
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 5)


# =====================================================================
# (c) The corpus
# =====================================================================

_CORPUS_DIRS = ("examples", "tests/conformance", "tests/probes")


def corpus_programs() -> list[Path]:
    """Every ``.vera`` source under the corpus roots, at any depth."""
    found: list[Path] = []
    for d in _CORPUS_DIRS:
        found.extend(sorted((_ROOT / d).rglob("*.vera")))
    return found


def corpus_outcome(path: Path) -> Outcome:
    """*path* through the pipeline, its imports resolved beside it."""
    return build(path, path.read_text(encoding="utf-8"), path.parent)


_USER_EFFECT = (
    "a user-declared effect in a function's row is not compilable: the "
    "function is the E603 skip spec §11.17 and SKILL.md name"
)
_UNINSTANTIATED_GENERIC = (
    "a library module compiled as the entry: its `forall` function has no "
    "instantiation in the program, so there is no concrete signature to emit "
    "— its clones are emitted where an importer calls it"
)

#: Corpus programs the checker accepts and code generation still refuses,
#: for a reason OUTSIDE this class.  Keyed by path; the value is the exact
#: refusal signature (:attr:`Outcome.signature`), so an entry cannot hide a
#: new drop in the same file.
KNOWN_CHECK_GREEN_REFUSALS: dict[str, tuple[tuple[str, ...], str]] = {
    "examples/effect_handler.vera": (("E603",), _USER_EFFECT),
    "examples/maximum_syntax.vera": (("E603", "E603"), _USER_EFFECT),
    "tests/conformance/ch03_typed_holes.vera": (
        ("E614", "missing-export"),
        "a typed hole is a W001 warning at check and refused at compile — "
        "spec §4.17 makes that the contract of `?`",
    ),
    "tests/conformance/ch08_module_prelude_adt_contention_rejected.vera": (
        ("E621", "missing-export", "missing-export"),
        "a conformance NEGATIVE whose manifest names the compile stage "
        "(`expected_error_stage: compile`): the checker accepts it by design",
    ),
    "tests/conformance/ch08_ambiguous_import_lib_bool.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/conformance/ch08_ambiguous_import_lib_int.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/conformance/ch08_cross_module_generic_lib.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/conformance/ch08_module_generic_diamond_base.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/probes/state_handlers/checker_gates/e533_uninstantiated.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/probes/state_handlers/checker_gates/e533lib.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/probes/state_handlers/checker_gates/loclib.vera": (
        ("E604",), _UNINSTANTIATED_GENERIC),
    "tests/probes/state_handlers/checker_gates/p2c_matching_refined.vera": (
        ("E602", "E620", "missing-export", "missing-export"),
        "an inline refinement literal as a State<T> argument is not "
        "compilable — spec §7.5 and SKILL.md say to name it with an alias",
    ),
    "tests/probes/state_handlers/clause_scoping/p15_resume_in_with.vera": (
        ("E602", "E620", "missing-export"),
        "`resume(...)` inside a `with` state-update has no effect, and code "
        "generation refuses it rather than dropping the resume silently",
    ),
    "tests/probes/state_handlers/clause_scoping/p_effparams.vera": (
        ("E602", "missing-export"),
        "a handler for a user-declared effect: only State<T> and Exn<E> "
        "handlers lower (user effects are the E603 limitation)",
    ),
    "tests/probes/state_handlers/old_state/p15_old_state_nested_alias.vera": (
        ("E602", "E602", "missing-export", "missing-export"),
        "a `let` of a parameterised alias (`let @Id<Nat>`) has no WASM "
        "representation in code generation, single-file as well — a "
        "different mechanism from this class's two",
    ),
}


@pytest.fixture(scope="module")
def outcomes() -> dict[str, Outcome]:
    """Every corpus program through the pipeline, once per test run."""
    return {
        p.relative_to(_ROOT).as_posix(): corpus_outcome(p)
        for p in corpus_programs()
    }


class TestCorpusCheckImpliesCompile:
    """(c): every corpus program the checker accepts, code generation builds."""

    def test_the_sweep_is_not_vacuous(
        self, outcomes: dict[str, Outcome],
    ) -> None:
        """The corpus is large, and most of it is accepted and compiled."""
        accepted = [k for k, o in outcomes.items() if o.accepted]
        assert len(outcomes) > 400, len(outcomes)
        assert len(accepted) > 300, len(accepted)

    def test_every_accepted_program_compiles(
        self, outcomes: dict[str, Outcome],
    ) -> None:
        """No accepted program is refused, unless the roster says why."""
        unexplained = {
            path: out.describe()
            for path, out in outcomes.items()
            if out.accepted and not out.compiles_clean
            and path not in KNOWN_CHECK_GREEN_REFUSALS
        }
        assert not unexplained, unexplained

    def test_the_roster_is_exact(
        self, outcomes: dict[str, Outcome],
    ) -> None:
        """Every entry is still accepted and refused with exactly its codes.

        A stale entry — a program since fixed, or refused at check now —
        fails here, so the roster cannot outlive what it explains.
        """
        for path, (codes, reason) in KNOWN_CHECK_GREEN_REFUSALS.items():
            assert reason
            out = outcomes.get(path)
            assert out is not None, f"{path}: no longer in the corpus"
            assert out.accepted, f"{path}: refused at check now"
            assert out.signature == codes, (path, out.signature, codes)


# =====================================================================
# (d) Handler-clause State operations (#1233)
# =====================================================================
#
# A `get`/`put` in a handler clause body is the ENCLOSING context's
# operation (spec §7.5.2), lowered by inlining the clause where an
# operation reaches it.  Code generation refuses the ones it cannot lower
# — a cell shadowed by a same-family cell pushed since (#1233), and a
# re-entry chain past STATE_CLAUSE_INLINE_DEPTH_CAP — and the checker now
# refuses the same ones with E339.  Two derivations of one decision, so the
# proof is a DIFFERENTIAL: every cell is compiled past the check, and the
# checker's E339 must coincide with code generation's own refusal, while a
# cell neither refuses must compile clean.

#: The cell families the nests are built from.  Two integer families, so a
#: `get(())` result types in every position whichever cell it reaches.
_FAMILIES = ("Int", "Nat")

#: A clause-body refusal code generation makes for exactly this rule.
_GATE_MARKERS = ("the host cell intrinsics address only", "nest more than")


def _handler(family: str, put_clause: str, body: str,
             get_clause: str = "resume(@{F}.0)",
             put_with: str | None = None) -> str:
    get_clause = get_clause.replace("{F}", family)
    with_part = f" with @{family} = {put_with}" if put_with else ""
    return (
        f"handle[State<{family}>](@{family} = 0) {{\n"
        f"    get(@Unit) -> {{ {get_clause} }},\n"
        f"    put(@{family}) -> {{ {put_clause} }}{with_part}\n"
        f"  }} in {{\n    {body}\n  }}"
    )


@dataclass(frozen=True)
class NestCell:
    """One nesting shape: a row, a nest of handlers, an operation's level."""

    row: str
    families: tuple[str, ...]
    #: Which handler's `put` clause holds the operation under test.
    level: int
    #: `direct`: a `put` in that handler's own body inlines the clause;
    #: `chain`: every inner handler's `put` clause routes outward, so the
    #: innermost `put` inlines the clause under every inner cell.
    trigger: str
    op: str

    @property
    def label(self) -> str:
        return (f"{self.row}|{'/'.join(self.families)}|L{self.level}|"
                f"{self.trigger}|{self.op}")

    def source(self) -> str:
        body = "put(1);\n    1"
        for i in reversed(range(len(self.families))):
            fam = self.families[i]
            if i == self.level:
                clause = f"{self.op};\n resume(())"
            elif self.trigger == "chain" and i > self.level:
                clause = "put(1);\n resume(())"
            else:
                clause = "resume(())"
            if i == self.level and self.trigger == "direct":
                body = f"put(1);\n    {body}"
            body = _handler(fam, clause, body)
        return (
            f"public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            f"  effects({self.row})\n{{\n  {body}\n}}\n" + _MAIN0
        )


def _nest_cells() -> tuple[NestCell, ...]:
    cells: list[NestCell] = []
    nests: list[tuple[str, ...]] = [
        tuple(fams) for k in (1, 2, 3)
        for fams in itertools.product(_FAMILIES, repeat=k)
    ]
    # The shadowing cell need not be the adjacent one: in an Int/Nat/Int/Nat
    # nest the third level's clause routes to the second, whose cell the
    # fourth's shadows through the chain.
    nests.append(("Int", "Nat", "Int", "Nat"))
    for row in ("pure", "<State<Int>>"):
        for fams in nests:
            for level in range(len(fams)):
                if row == "pure" and level == 0:
                    continue  # the outermost clause's op reaches no cell
                for trigger in ("direct", "chain"):
                    if trigger == "chain" and level == len(fams) - 1:
                        continue  # the innermost has nothing to chain from
                    for op in ("put(1)", "State.put(1)"):
                        cells.append(NestCell(row, fams, level, trigger, op))
    return tuple(cells)


NEST_CELLS = _nest_cells()


@dataclass(frozen=True)
class ClausePosition:
    """Where in a clause body the operation sits."""

    label: str
    fields: frozenset[tuple[str, str]]
    #: The clause body, with `{OP}` for a `get(())` whose value is used.
    body: str


CLAUSE_POSITIONS: tuple[ClausePosition, ...] = (
    ClausePosition("let", _f(("LetStmt", "value")),
                   "let @Int = {OP};\n resume(())"),
    ClausePosition("statement", _f(("ExprStmt", "expr")),
                   "{OP};\n resume(())"),
    ClausePosition("operand", _f(("BinaryExpr", "left"),
                                 ("BinaryExpr", "right")),
                   "let @Bool = {OP} > 0;\n resume(())"),
    ClausePosition("negation", _f(("UnaryExpr", "operand")),
                   "let @Int = -{OP};\n resume(())"),
    ClausePosition("if condition", _f(("IfExpr", "condition")),
                   "let @Int = if {OP} > 0 then { 1 } else { 2 };\n"
                   " resume(())"),
    ClausePosition("if branch", _f(("IfExpr", "then_branch"),
                                   ("IfExpr", "else_branch")),
                   "let @Int = if true then { {OP} } else { 0 };\n"
                   " resume(())"),
    ClausePosition("match scrutinee", _f(("MatchExpr", "scrutinee")),
                   "let @Int = match {OP} {\n 0 -> 1,\n _ -> 2\n };\n"
                   " resume(())"),
    ClausePosition("match arm", _f(("MatchArm", "body")),
                   "let @Int = match 1 {\n 0 -> 0,\n _ -> {OP}\n };\n"
                   " resume(())"),
    ClausePosition("call argument", _f(("FnCall", "args")),
                   "let @Int = abs({OP});\n resume(())"),
    ClausePosition("constructor argument", _f(("ConstructorCall", "args")),
                   "let @Option<Int> = Some({OP});\n resume(())"),
    ClausePosition("destructured tuple", _f(("LetDestruct", "value"),
                                            ("ConstructorCall", "args")),
                   "let Tuple<@Int, @Int> = Tuple({OP}, 1);\n resume(())"),
    ClausePosition("array element", _f(("ArrayLit", "elements")),
                   "let @Array<Int> = [{OP}];\n resume(())"),
    ClausePosition("index", _f(("IndexExpr", "index")),
                   "let @Array<Int> = [7, 8];\n"
                   " let @Int = @Array<Int>.0[{OP}];\n resume(())"),
    ClausePosition("interpolation", _f(("InterpolatedString", "parts")),
                   'let @String = "\\({OP})";\n resume(())'),
    ClausePosition("assert", _f(("AssertExpr", "expr")),
                   "assert({OP} >= 0);\n resume(())"),
    # Code generation emits nothing for an `assume` (the verifier's axiom),
    # so an operation inside one is never lowered and never refused.
    ClausePosition("assume", _f(("AssumeExpr", "expr")),
                   "assume({OP} >= 0);\n resume(())"),
    ClausePosition("block", _f(("Block", "expr")),
                   "let @Int = {\n {OP}\n };\n resume(())"),
    ClausePosition("nested Exn body", _f(("HandleExpr", "body")),
                   "let @Int = handle[Exn<Bool>] {\n throw(@Bool) -> 0\n }"
                   " in {\n {OP}\n };\n resume(())"),
    ClausePosition("nested Exn clause", _f(("HandlerClause", "body")),
                   "let @Int = handle[Exn<Bool>] {\n throw(@Bool) -> {OP}\n }"
                   " in {\n throw(true)\n };\n resume(())"),
    ClausePosition("nested State init", _f(("HandlerState", "init_expr")),
                   "let @Int = handle[State<Bool>](@Bool = {OP} > 0) {\n"
                   " get(@Unit) -> { resume(@Bool.0) },\n"
                   " put(@Bool) -> { resume(()) }\n } in {\n 0\n };\n"
                   " resume(())"),
    ClausePosition("with clause", _f(("HandlerClause", "state_update")),
                   "{OP} + 0"),
    ClausePosition("lambda", _f(("AnonFn", "body")),
                   "let @Array<Int> = array_map([1], fn(@Int -> @Int) "
                   "effects(pure) { {OP} });\n resume(())"),
    ClausePosition("resume argument", frozenset(), "resume({OP})"),
)

#: AST expression fields a clause body cannot hold, and why.
CLAUSE_POSITION_EXCLUSIONS: dict[tuple[str, str], str] = {
    ("Requires", "expr"): "a contract, outside every body",
    ("Ensures", "expr"): "a contract, outside every body",
    ("Decreases", "exprs"): "a contract, outside every body",
    ("Invariant", "expr"): "a data invariant, outside every body",
    ("DataDecl", "invariant"): "a data invariant, outside every body",
    ("RefinementType", "predicate"): "a type's predicate, not a body",
    ("FnDecl", "body"): "a declaration's body, not a clause's",
    ("ForallExpr", "domain"): "a quantifier is contract-only",
    ("ForallExpr", "predicate"): "a quantifier is contract-only",
    ("ExistsExpr", "domain"): "a quantifier is contract-only",
    ("ExistsExpr", "predicate"): "a quantifier is contract-only",
    ("ModuleCall", "args"): "a single-file cell imports no module",
    ("QualifiedCall", "args"): "the `State.put` spelling is the shape "
                               "matrix's dimension",
    ("IndexExpr", "collection"): "the operation yields an integer, not a "
                                 "collection",
}


@dataclass(frozen=True)
class PositionCell:
    """One clause-body position, in a shadowed or an unshadowed shape."""

    position: ClausePosition
    shadowed: bool
    op: str

    @property
    def label(self) -> str:
        return (f"{self.position.label}|"
                f"{'shadowed' if self.shadowed else 'distinct'}|{self.op}")

    def source(self) -> str:
        # The function's row is the operation's cell; the handler's cell is
        # the same family (shadowed) or a different one (distinct).
        row_family = "Int"
        family = "Int" if self.shadowed else "Nat"
        clause = self.position.body.replace("{OP}", self.op).replace(
            "{F}", family)
        if self.position.label == "resume argument":
            handler = _handler(family, "resume(())",
                               "let @Nat = get(());\n    1",
                               get_clause=clause)
        elif self.position.label == "with clause":
            handler = _handler(family, "resume(())", "put(1);\n    1",
                               put_with=clause)
        else:
            handler = _handler(family, clause, "put(1);\n    1")
        return (
            f"public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            f"  effects(<State<{row_family}>>)\n{{\n  {handler}\n}}\n"
            + _MAIN0
        )


POSITION_CELLS: tuple[PositionCell, ...] = tuple(
    PositionCell(position, shadowed, op)
    for position in CLAUSE_POSITIONS
    for shadowed in (True, False)
    for op in ("get(())", "State.get(())")
)


def _gate_refused(outcome: Outcome) -> bool:
    """Whether code generation's own clause-op gate refused ``f``."""
    return any(
        d.error_code == "E602" and "'f'" in d.description
        and any(m in d.description for m in _GATE_MARKERS)
        for d in outcome.drops
    )


def _differential(outcome: Outcome) -> None:
    """E339 at check exactly when code generation's gate refuses."""
    codes = {d.error_code for d in outcome.check_errors}
    others = codes - {"E339"}
    assert not others, outcome.describe()
    refused = "E339" in codes
    assert refused == _gate_refused(outcome), outcome.describe()
    if not refused:
        assert outcome.compiles_clean, outcome.describe()


def _depth_chain(levels: int) -> str:
    """*levels* handlers over distinct cells, each clause re-entering the
    next one out, so the innermost `put` inlines *levels* clauses."""
    decls = "".join(f"private data D{i} {{ M{i} }}\n\n"
                    for i in range(levels))
    body = f"put(M{levels - 1});\n    1"
    for i in reversed(range(levels)):
        clause = "resume(())" if i == 0 else f"put(M{i - 1});\n resume(())"
        body = (
            f"handle[State<D{i}>](@D{i} = M{i}) {{\n"
            f"    get(@Unit) -> {{ resume(@D{i}.0) }},\n"
            f"    put(@D{i}) -> {{ {clause} }}\n"
            f"  }} in {{\n    {body}\n  }}"
        )
    return (
        decls + "public fn f(@Int -> @Int)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  " + body + "\n}\n" + _MAIN0
    )


class TestClauseOperationMatrix:
    """(d): #1233 — the checker refuses exactly what code generation can't."""

    @pytest.mark.parametrize("levels", (
        STATE_CLAUSE_INLINE_DEPTH_CAP, STATE_CLAUSE_INLINE_DEPTH_CAP + 1,
    ))
    def test_reentry_depth(self, levels: int, tmp_path: Path) -> None:
        """At the cap the chain compiles; one level past it both refuse."""
        outcome = pipeline(tmp_path, {"main.vera": _depth_chain(levels)},
                           past_check=True)
        _differential(outcome)
        refused = "E339" in {d.error_code for d in outcome.check_errors}
        assert refused == (levels > STATE_CLAUSE_INLINE_DEPTH_CAP)

    def test_every_clause_position_has_a_cell(self) -> None:
        """Every AST expression field is a cell or an excluded position."""
        fields = {f for f in ast_expression_fields()
                  if not f[0].startswith("_")}
        claimed = frozenset().union(*(p.fields for p in CLAUSE_POSITIONS))
        excluded = frozenset(CLAUSE_POSITION_EXCLUSIONS)
        assert not claimed & excluded, sorted(claimed & excluded)
        assert not fields - claimed - excluded, sorted(
            fields - claimed - excluded)
        assert not (claimed | excluded) - fields, sorted(
            (claimed | excluded) - fields)

    def test_the_matrix_refuses_and_accepts(self, tmp_path: Path) -> None:
        """Not vacuous: both verdicts occur, and the known shapes land."""
        verdicts = {}
        for cell in NEST_CELLS:
            out = pipeline(tmp_path / str(len(verdicts)),
                           {"main.vera": cell.source()}, past_check=True)
            verdicts[cell.label] = "E339" in {
                d.error_code for d in out.check_errors}
        assert any(verdicts.values()) and not all(verdicts.values())
        # The #1233 report: Int in Int, and a handler in a function whose
        # row declares its own cell.
        assert verdicts["pure|Int/Int|L1|direct|put(1)"]
        assert verdicts["<State<Int>>|Int|L0|direct|put(1)"]
        # Different families never shadow each other.
        assert not verdicts["pure|Int/Nat|L1|direct|put(1)"]
        assert not verdicts["<State<Int>>|Nat|L0|direct|put(1)"]
        # At a distance: Int/Nat/Int/Nat, the third's clause reaches the
        # second, shadowed by the fourth through the chain.
        assert verdicts["pure|Int/Nat/Int/Nat|L2|chain|put(1)"]

    @pytest.mark.parametrize("cell", NEST_CELLS, ids=lambda c: c.label)
    def test_nesting_shape(self, cell: NestCell, tmp_path: Path) -> None:
        _differential(pipeline(tmp_path, {"main.vera": cell.source()},
                               past_check=True))

    @pytest.mark.parametrize("cell", POSITION_CELLS, ids=lambda c: c.label)
    def test_clause_position(self, cell: PositionCell, tmp_path: Path) -> None:
        outcome = pipeline(tmp_path, {"main.vera": cell.source()},
                           past_check=True)
        if cell.position.label == "lambda":
            # A closure is lifted with no State cells, so the checker refuses
            # the operation inside it for its own reasons; the rule here is
            # only that no E339 is claimed for it.
            assert "E339" not in {d.error_code for d in outcome.check_errors}
            return
        _differential(outcome)
        emitted = cell.position.label != "assume"
        assert ("E339" in {d.error_code for d in outcome.check_errors}) \
            == (cell.shadowed and emitted), outcome.describe()


# =====================================================================
# (e) Nested generic calls, in the entry file and in a module (#1509)
# =====================================================================
#
# Code generation compiles a generic once per concrete type it is called
# with, and DISCOVERY names each specialisation from the types of the
# arguments at the call.  Where its own walker cannot name an argument — a
# nested generic call is the common one — it asks the CHECKER, whose tables
# are keyed by span, one table per file.  Discovery asked the ENTRY file's
# table for every body it walked, so a nested call in a module's body got no
# answer, the type variable fell to the phantom default, and the call site —
# compiled against the module's own table — named a specialisation nothing
# emitted: E602, then E620 up the call graph, on a program that ran as the
# entry file.
#
# The cells: every prelude generic as the OUTER call — enumerated from the
# prelude itself — plus user generics that bind a variable directly and only
# through a type argument, around every producer of the outer's first
# parameter type (the prelude's own, enumerated likewise, and a user
# generic), written in three places — a function, a generic function and a
# `where` helper — in the entry file and in a module.  Every cell must
# compile clean and run to its value, and the verifier must discover every
# specialisation code generation emits (the #732 differential), with the
# checker's tables threaded to both as the CLI threads them.

_NC = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def prelude_generics() -> dict[str, ast.FnDecl]:
    """The prelude's generic functions, as the prelude declares them."""
    from vera.prelude import inject_prelude

    program = parse_to_ast(
        "public fn main(@Unit -> @Int)\n" + _NC + "{\n  1\n}\n")
    inject_prelude(program)
    return {
        tld.decl.name: tld.decl for tld in program.declarations
        if isinstance(tld.decl, ast.FnDecl) and tld.decl.forall_vars
    }


def _head(te: ast.TypeExpr) -> str | None:
    """``Option`` or ``Result`` for a type written as one, else ``None``."""
    if isinstance(te, ast.NamedType) and te.name in ("Option", "Result"):
        return te.name
    return None


#: Each prelude generic that returns an ``Option`` or a ``Result``, called as
#: the INNER producer: an expression of that type whose payload is 2.
_PRELUDE_PRODUCERS: dict[str, str] = {
    "option_map":
        "option_map(Some(1), fn(@Int -> @Int) effects(pure) "
        "{ @Int.0 + 1 })",
    "option_and_then":
        "option_and_then(Some(1), fn(@Int -> @Option<Int>) effects(pure) "
        "{ Some(@Int.0 + 1) })",
    "result_map":
        'result_map(parse_int("1"), fn(@Int -> @Int) effects(pure) '
        "{ @Int.0 + 1 })",
}

#: Each prelude generic as the OUTER call around a producer ``{P}``, closed
#: to an ``Int``, with the value it computes from a payload of 2.
_PRELUDE_OUTERS: dict[str, tuple[str, int]] = {
    "option_unwrap_or": ("option_unwrap_or({P}, 0)", 2),
    "option_map": (
        "option_unwrap_or(option_map({P}, fn(@Int -> @Int) effects(pure) "
        "{ @Int.0 * 10 }), 0)", 20),
    "option_and_then": (
        "option_unwrap_or(option_and_then({P}, fn(@Int -> @Option<Int>) "
        "effects(pure) { Some(@Int.0 * 10) }), 0)", 20),
    "result_unwrap_or": ("result_unwrap_or({P}, 0)", 2),
    "result_map": (
        "result_unwrap_or(result_map({P}, fn(@Int -> @Int) effects(pure) "
        "{ @Int.0 * 10 }), 0)", 20),
}

#: The user generics a cell declares beside its expression, each only where
#: the expression calls it (an entry file's generic that nothing instantiates
#: is its own E604): a producer per head, an identity (its variable bound
#: DIRECTLY by the nested call), and an unwrap per head (``E`` bound only
#: through ``Result<T, E>``).
_USER_GENERICS: dict[str, str] = {
    "justg": "private forall<T> fn justg(@T -> @Option<T>)\n" + _NC
             + "{\n  Some(@T.0)\n}\n\n",
    "okg": "private forall<T> fn okg(@T -> @Result<T, String>)\n" + _NC
           + "{\n  Ok(@T.0)\n}\n\n",
    "idg": "private forall<T> fn idg(@T -> @T)\n" + _NC + "{\n  @T.0\n}\n\n",
    "opt_or": "private forall<T> fn opt_or(@Option<T>, @T -> @T)\n" + _NC
              + "{\n  match @Option<T>.0 {\n    Some(@T) -> @T.0,\n"
              "    None -> @T.0\n  }\n}\n\n",
    "res_or": "private forall<T, E> fn res_or(@Result<T, E>, @T -> @T)\n"
              + _NC + "{\n  match @Result<T, E>.0 {\n    Ok(@T) -> @T.0,\n"
              "    Err(@E) -> @T.0\n  }\n}\n\n",
}

#: The same generics, public in a library module ``gl`` and called
#: QUALIFIED from the namespace the expression is written in.
_GL = (
    "module gl;\n\n"
    + _USER_GENERICS["justg"].replace("private ", "public ", 1)
    + _USER_GENERICS["okg"].replace("private ", "public ", 1)
    + _USER_GENERICS["idg"].replace("private ", "public ", 1)
)

_USER_PRODUCERS: dict[str, dict[str, str]] = {
    "Option": {"justg": "justg(2)", "gl::justg": "gl::justg(2)"},
    "Result": {"okg": "okg(2)", "gl::okg": "gl::okg(2)"},
}

_USER_OUTERS: dict[str, dict[str, tuple[str, int]]] = {
    "Option": {
        "idg": ("option_unwrap_or(idg({P}), 0)", 2),
        "gl::idg": ("option_unwrap_or(gl::idg({P}), 0)", 2),
        "opt_or": ("opt_or({P}, 0)", 2),
    },
    "Result": {
        "idg": ("result_unwrap_or(idg({P}), 0)", 2),
        "gl::idg": ("result_unwrap_or(gl::idg({P}), 0)", 2),
        "res_or": ("res_or({P}, 0)", 2),
    },
}

#: Where the expression is written: a function, a generic function (so the
#: expression reaches discovery through a specialisation's body), and a
#: `where` helper — each in the entry file and in an imported module.
NEST_PLACES = ("function", "generic function", "where helper")


def _nested_body(place: str, expr: str) -> str:
    """``probe`` computing *expr* from *place*."""
    if place == "function":
        return ("public fn probe(@Unit -> @Int)\n" + _NC
                + "{\n  " + expr + "\n}\n")
    if place == "generic function":
        return ("private forall<T> fn viag(@T -> @Int)\n" + _NC
                + "{\n  " + expr + "\n}\n\n"
                "public fn probe(@Unit -> @Int)\n" + _NC
                + "{\n  viag(1)\n}\n")
    assert place == "where helper", place
    return ("public fn probe(@Unit -> @Int)\n" + _NC
            + "{\n  helper(1)\n}\nwhere {\n  fn helper(@Int -> @Int)\n"
            "    requires(true)\n    ensures(true)\n    effects(pure)\n"
            "  {\n    " + expr + "\n  }\n}\n")


_NEST_MAIN = "public fn main(@Unit -> @Int)\n" + _NC + "{\n  probe(())\n}\n"


@dataclass(frozen=True)
class NestedCallCell:
    outer: str
    producer: str
    expr: str
    value: int
    place: str
    in_module: bool

    @property
    def label(self) -> str:
        where = "module" if self.in_module else "entry"
        return f"{where}|{self.place}|{self.outer}({self.producer})"

    def files(self) -> dict[str, str]:
        unqualified = self.expr.replace("gl::", "gl.")
        used = "".join(
            decl for name, decl in _USER_GENERICS.items()
            if re.search(rf"(?<![\w.]){name}\(", unqualified)
        )
        body = used + _nested_body(self.place, self.expr)
        imports = "import gl;\n\n" if "gl::" in self.expr else ""
        library = {"gl.vera": _GL} if imports else {}
        if not self.in_module:
            return {**library, "main.vera": imports + body + "\n" + _NEST_MAIN}
        return {
            **library,
            "mb.vera": "module mb;\n\n" + imports + body,
            "main.vera": "import mb(probe);\n\n" + _NEST_MAIN,
        }


def _nested_shapes() -> list[tuple[str, str, str, int]]:
    """``(outer, producer, expression, value)`` for every pairing."""
    decls = prelude_generics()
    producers: dict[str, dict[str, str]] = {
        head: dict(user) for head, user in _USER_PRODUCERS.items()
    }
    for name, decl in decls.items():
        head = _head(decl.return_type)
        if head is not None:
            producers[head][name] = _PRELUDE_PRODUCERS[name]
    outers: dict[str, dict[str, tuple[str, int]]] = {
        head: dict(user) for head, user in _USER_OUTERS.items()
    }
    for name, decl in decls.items():
        head = _head(decl.params[0])
        assert head is not None, f"{name}: first parameter is not an ADT"
        outers[head][name] = _PRELUDE_OUTERS[name]
    shapes = []
    for head in sorted(outers):
        for outer, (template, value) in sorted(outers[head].items()):
            for producer, call in sorted(producers[head].items()):
                shapes.append(
                    (outer, producer, template.replace("{P}", call), value))
    return shapes


NESTED_CALL_CELLS: tuple[NestedCallCell, ...] = tuple(
    NestedCallCell(outer, producer, expr, value, place, in_module)
    for outer, producer, expr, value in _nested_shapes()
    for place in NEST_PLACES
    for in_module in (False, True)
)


def _ctor_nested_cells() -> tuple[NestedCallCell, ...]:
    """Every producer, unwrapped to its payload (2) and passed through a
    constructor argument of `option_unwrap_or`, inside a user generic."""
    cells = []
    producers = {
        head: {**_USER_PRODUCERS[head]} for head in _USER_PRODUCERS
    }
    for name, call in _PRELUDE_PRODUCERS.items():
        head = _head(prelude_generics()[name].return_type)
        assert head is not None
        producers[head][name] = call
    unwrap = {"Option": "option_unwrap_or", "Result": "result_unwrap_or"}
    for head in sorted(producers):
        for producer, call in sorted(producers[head].items()):
            expr = (f"idg(option_unwrap_or(Some({unwrap[head]}({call}, 0)), "
                    "0))")
            for place in NEST_PLACES:
                for in_module in (False, True):
                    cells.append(NestedCallCell(
                        "idg(option_unwrap_or(Some(...)))", producer, expr,
                        2, place, in_module))
    return tuple(cells)


CTOR_NESTED_CELLS: tuple[NestedCallCell, ...] = _ctor_nested_cells()


def _unwrapped_cells() -> tuple[NestedCallCell, ...]:
    """Every producer, unwrapped to its payload (2) by the prelude and
    passed straight to a user generic's bare variable (#1515): `idg`'s `T`
    is bound by a call whose own `E` no argument determines."""
    producers: dict[str, dict[str, str]] = {
        "Option": {**_USER_PRODUCERS["Option"], "Some": "Some(2)"},
        "Result": {**_USER_PRODUCERS["Result"], "Ok": "Ok(2)"},
    }
    for name, call in _PRELUDE_PRODUCERS.items():
        head = _head(prelude_generics()[name].return_type)
        assert head is not None
        producers[head][name] = call
    unwrap = {"Option": "option_unwrap_or", "Result": "result_unwrap_or"}
    return tuple(
        NestedCallCell(f"idg({unwrap[head]}(...))", producer,
                       f"idg({unwrap[head]}({call}, 0))", 2, place, in_module)
        for head in sorted(producers)
        for producer, call in sorted(producers[head].items())
        for place in NEST_PLACES
        for in_module in (False, True)
    )


UNWRAPPED_CELLS: tuple[NestedCallCell, ...] = _unwrapped_cells()


def _emitted_and_discovered(
    tmp_path: Path, files: dict[str, str],
) -> tuple[set[tuple[str, tuple[str, ...]]], set[tuple[str, tuple[str, ...]]]]:
    """``(what code generation emits, what the verifier discovers)``.

    Both built with the checker's tables threaded exactly as the CLI threads
    them — the entry file's, and each module's own.
    """
    from vera.codegen.core import CodeGenerator
    from vera.verifier import ContractVerifier

    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    source = files["main.vera"]
    program = parse_to_ast(source)
    resolved = ModuleResolver(_root=tmp_path).resolve_imports(
        program, main_path)
    _diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    gen = CodeGenerator(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    gen.compile_program(parse_to_ast(source))
    verifier = ContractVerifier(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    verifier.register_program(parse_to_ast(source))
    discovered = {
        (name, types)
        for name, all_types in verifier._instances.items()
        for types in all_types
    }
    return set(gen._emitted_instances), discovered


def uncovered_instances(
    emitted: set[tuple[str, tuple[str, ...]]],
    discovered: set[tuple[str, tuple[str, ...]]],
) -> set[tuple[str, tuple[str, ...]]]:
    """What code generation emits that the verifier did not discover.

    The verifier names scalars more precisely than code generation's WAT
    collapse (``Nat`` for ``Int``), so its set is normalised through that
    collapse first — the #732 differential's own rule.
    """
    collapse = {"Nat": "Int", "Byte": "Bool"}

    def norm(types: tuple[str, ...]) -> tuple[str, ...]:
        # Code generation names a module's data type whose name another
        # namespace also declares by its owner-qualified symbol
        # (`mod$mb$Shape`, #1317); the verifier names it as its module
        # spells it.  Both denote the one type.
        return tuple(
            collapse.get(t, t) for t in (_OWNER_PREFIX.sub("", t) for t in types)
        )

    seen = {(name, norm(types)) for name, types in discovered}
    return {(n, t) for n, t in emitted if (n, norm(t)) not in seen}


_OWNER_PREFIX = re.compile(r"mod\$(?:\w+\$)+")


class TestNestedGenericCalls:
    """(e): a nested generic call compiles wherever it is written (#1509)."""

    def test_every_prelude_generic_is_an_outer_and_a_producer_where_it_can_be(
        self,
    ) -> None:
        """The prelude's generics are the matrix's, enumerated not listed."""
        decls = prelude_generics()
        assert set(_PRELUDE_OUTERS) == set(decls), sorted(decls)
        producing = {n for n, d in decls.items() if _head(d.return_type)}
        assert set(_PRELUDE_PRODUCERS) == producing, sorted(producing)
        outers = {c.outer for c in NESTED_CALL_CELLS}
        assert set(decls) <= outers, sorted(set(decls) - outers)

    def test_the_reported_program_is_a_cell(self) -> None:
        labels = {c.label for c in NESTED_CALL_CELLS}
        assert "module|function|result_unwrap_or(result_map)" in labels

    @pytest.mark.parametrize("cell", NESTED_CALL_CELLS, ids=lambda c: c.label)
    def test_compiles_and_runs_wherever_it_is_written(
        self, cell: NestedCallCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert emitted, "no specialisation emitted: the cell is vacuous"
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    @pytest.mark.parametrize("cell", CTOR_NESTED_CELLS, ids=lambda c: c.label)
    def test_nested_in_a_constructor_argument(
        self, cell: NestedCallCell, tmp_path: Path,
    ) -> None:
        """A generic call nested inside a CONSTRUCTOR argument of another
        (#1509).  Discovery named it without the generics it knows, so the
        nested call answered its callee's raw return — the prelude's own
        type variable — and the call site's rewrite, whose generic arm gave
        up on a phantom variable, answered the checker's `Nat`; neither was
        the clone the other emitted.  In the entry file as in a module."""
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    @pytest.mark.parametrize("cell", UNWRAPPED_CELLS, ids=lambda c: c.label)
    def test_unwrapped_into_a_bare_variable(
        self, cell: NestedCallCell, tmp_path: Path,
    ) -> None:
        """#1515's shape: `idg(result_unwrap_or(Ok(3), 0))`.  The call site
        named `idg` from the checker's `Nat` (its generic arm gave up on the
        phantom `E`) where discovery named it from the bound return, `Int`.
        The call site now names a generic call's result as discovery does;
        the two derivations of the type arguments remain two (#1515)."""
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    def test_the_differential_can_fail(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Not vacuous: a verifier reading the entry file's table for a
        module's body discovers a specialisation code generation does not
        emit, and misses the one it does."""
        from vera.verifier import ContractVerifier

        cell = next(c for c in NESTED_CALL_CELLS
                    if c.label == "module|function|result_unwrap_or(result_map)")
        real = ContractVerifier.__init__

        def entry_table_only(self, *args, **kwargs):  # type: ignore[no-untyped-def]
            kwargs.pop("module_artifacts", None)
            real(self, *args, **kwargs)

        monkeypatch.setattr(ContractVerifier, "__init__", entry_table_only)
        emitted, discovered = _emitted_and_discovered(tmp_path, cell.files())
        assert uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")


# =====================================================================
# (f) Generics instantiated at a user data type (#1511)
# =====================================================================
#
# A mono clone is registered and compiled in the namespace its generic was
# DECLARED in — the prelude's for a combinator, the module's for a module's
# generic — while its type arguments are named in the namespace that
# instantiated it.  The declaring namespace's data-type membership did not
# hold the instantiating namespace's types, so `option_unwrap_or` at a user
# `Shape` had a parameter with no WASM representation and was skipped
# (E604), taking every caller with it (E620), on a check-green program: in a
# single file, in a module, and at a module's owner-qualified type
# (`mod$mb$Shape`, when the entry declares a `Shape` of its own).
#
# The cells: every prelude generic (enumerated from the prelude) producing a
# `Shape`, flat and nested (the same value passed through
# `option_unwrap_or` and a user generic), written in the entry file, in a
# module, and in a module whose `Shape` is owner-qualified; and a library
# module's generics instantiated at the entry's type and at a module's.

_SHAPE_DECLS = (
    "private data Shape {\n  Circle(Int),\n  Square(Int)\n}\n\n"
    "private fn size(@Shape -> @Int)\n" + _NC
    + "{\n  match @Shape.0 {\n    Circle(@Int) -> @Int.0,\n"
    "    Square(@Int) -> @Int.0 * 10\n  }\n}\n\n"
)

_TO_SHAPE = "fn(@Int -> @Shape) effects(pure) { Circle(@Int.0) }"

#: Each prelude generic as a `Shape`-valued expression whose value is
#: `Circle(4)` (so `size` of it is 4).
_PRELUDE_AT_SHAPE: dict[str, str] = {
    "option_unwrap_or": "option_unwrap_or(Some(Circle(4)), Square(3))",
    "option_map":
        f"option_unwrap_or(option_map(Some(4), {_TO_SHAPE}), Square(3))",
    "option_and_then":
        "option_unwrap_or(option_and_then(Some(4), fn(@Int -> @Option<Shape>) "
        "effects(pure) { Some(Circle(@Int.0)) }), Square(3))",
    "result_unwrap_or": "result_unwrap_or(Ok(Circle(4)), Square(3))",
    "result_map":
        f'result_unwrap_or(result_map(parse_int("4"), {_TO_SHAPE}), '
        "Square(3))",
}

#: A library module's generics, called qualified at the namespace's `Shape`.
_GL_AT_SHAPE: dict[str, str] = {
    "gl::idg": "gl::idg(Circle(4))",
    "gl::justg": "option_unwrap_or(gl::justg(Circle(4)), Square(3))",
}

AT_TYPE_PLACES = ("entry", "module", "module, owner-qualified")


@dataclass(frozen=True)
class AtTypeCell:
    generic: str
    shape: str          # "flat", "nested" or "scrutinee"
    place: str

    @property
    def nested(self) -> bool:
        return self.shape == "nested"

    @property
    def label(self) -> str:
        return f"{self.place}|{self.shape}|{self.generic}"

    def expr(self) -> str:
        inner = {**_PRELUDE_AT_SHAPE, **_GL_AT_SHAPE}[self.generic]
        if self.shape == "scrutinee":
            # The release-branch regression's shape: a direct `match` on the
            # instantiated call.
            return (f"match {inner} {{\n    Circle(@Int) -> @Int.0,\n"
                    "    Square(@Int) -> @Int.0 * 10\n  }")
        if self.nested:
            inner = f"idg(option_unwrap_or(Some({inner}), Square(3)))"
        return f"size({inner})"

    def files(self) -> dict[str, str]:
        imports = "import gl;\n\n" if "gl::" in self.generic else ""
        library = {"gl.vera": _GL} if imports else {}
        # An entry file's generic nothing instantiates is its own E604, so
        # `idg` is declared only where the nesting calls it.
        idg = _USER_GENERICS["idg"] if self.nested else ""
        body = (_SHAPE_DECLS + idg + "public fn probe(@Unit -> @Int)\n" + _NC
                + "{\n  " + self.expr() + "\n}\n")
        if self.place == "entry":
            return {**library,
                    "main.vera": imports + body + "\n" + _NEST_MAIN}
        entry_shape = (
            "private data Shape {\n  Tri(Int)\n}\n\n"
            if self.place == "module, owner-qualified" else ""
        )
        return {
            **library,
            "mb.vera": "module mb;\n\n" + imports + body,
            "main.vera": "import mb(probe);\n\n" + entry_shape + _NEST_MAIN,
        }


AT_TYPE_CELLS: tuple[AtTypeCell, ...] = tuple(
    AtTypeCell(generic, shape, place)
    for generic in (*sorted(_PRELUDE_AT_SHAPE), *sorted(_GL_AT_SHAPE))
    for shape in ("flat", "nested", "scrutinee")
    for place in AT_TYPE_PLACES
)


class TestGenericsAtUserTypes:
    """(f): a generic compiles at a data type its instantiator names (#1511)."""

    def test_every_prelude_generic_has_a_cell(self) -> None:
        assert set(_PRELUDE_AT_SHAPE) == set(prelude_generics())

    @pytest.mark.parametrize("cell", AT_TYPE_CELLS, ids=lambda c: c.label)
    def test_compiles_and_runs(
        self, cell: AtTypeCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 4)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert emitted, "no specialisation emitted: the cell is vacuous"
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    def test_the_owner_qualified_cell_is_owner_qualified(
        self, tmp_path: Path,
    ) -> None:
        """Not vacuous: the collision renames the module's `Shape`, so the
        clone is named for `mod$mb$Shape`."""
        cell = next(c for c in AT_TYPE_CELLS
                    if c.label == "module, owner-qualified|flat|option_unwrap_or")
        emitted, _discovered = _emitted_and_discovered(tmp_path, cell.files())
        assert ("option_unwrap_or", ("mod$mb$Shape",)) in emitted, emitted


#: A module that declares `Shape` for another namespace to use, and the
#: functions a namespace that never imports the type reaches it through.
_MS = (
    "module ms;\n\npublic data Shape {\n  Circle(Int),\n  Square(Int)\n}\n\n"
    "public fn size(@Shape -> @Int)\n" + _NC
    + "{\n  match @Shape.0 {\n    Circle(@Int) -> @Int.0,\n"
    "    Square(@Int) -> @Int.0 * 10\n  }\n}\n\n"
    "public fn mk(@Int -> @Shape)\n" + _NC + "{\n  Circle(@Int.0)\n}\n"
)

#: Each generic, by where it is declared and where its type variable sits,
#: as a `Shape`-valued expression over `{V}` (a `Shape`) and `{W}` (another).
_ORIGIN_GENERICS: dict[str, tuple[str, str]] = {
    # the prelude: a bare type variable as parameter and result
    "option_unwrap_or": ("", "option_unwrap_or(Some({V}), {W})"),
    # the prelude: the variable inside a pointer-represented type
    "option_map": ("", "option_unwrap_or(option_map(Some(4), "
                       "fn(@Int -> @Shape) effects(pure) { {V} }), {W})"),
    # a library module's generic, called qualified
    "gl::idg": ("import gl;\n", "gl::idg({V})"),
    # a library module's generic, imported by name
    "justg": ("import gl(justg);\n", "option_unwrap_or(justg({V}), {W})"),
    # the instantiating file's own generic
    "idg": ("", "idg({V})"),
}

#: Where the instantiating namespace gets `Shape` from.
_ORIGINS: dict[str, tuple[str, str, str]] = {
    # (import line, the value, the other value)
    "imported from a third module": (
        "import ms(Shape, size);\n", "Circle(4)", "Square(3)"),
    "never imported": ("import ms(mk, size);\n", "mk(4)", "mk(3)"),
}


@dataclass(frozen=True)
class TypeOriginCell:
    """A generic at a `Shape` the instantiating namespace did not declare."""

    generic: str
    origin: str
    place: str          # "entry" or "module"

    @property
    def label(self) -> str:
        return f"{self.place}|{self.origin}|{self.generic}"

    def files(self) -> dict[str, str]:
        gl_import, template = _ORIGIN_GENERICS[self.generic]
        ms_import, value, other = _ORIGINS[self.origin]
        expr = template.replace("{V}", value).replace("{W}", other)
        own = _USER_GENERICS["idg"] if self.generic == "idg" else ""
        body = (ms_import + gl_import + "\n" + own
                + "public fn probe(@Unit -> @Int)\n" + _NC
                + "{\n  size(" + expr + ")\n}\n")
        files = {"ms.vera": _MS}
        if gl_import:
            files["gl.vera"] = _GL
        if self.place == "entry":
            files["main.vera"] = body + "\n" + _NEST_MAIN
        else:
            files["mb.vera"] = "module mb;\n\n" + body
            files["main.vera"] = "import mb(probe);\n\n" + _NEST_MAIN
        return files


TYPE_ORIGIN_CELLS: tuple[TypeOriginCell, ...] = tuple(
    TypeOriginCell(generic, origin, place)
    for generic in _ORIGIN_GENERICS
    for origin in _ORIGINS
    for place in ("entry", "module")
    # `option_map`'s closure has to name `Shape`, which a namespace that
    # never imported it cannot (E136); the variable's position inside a
    # pointer-represented type is `justg`'s there.
    if not (generic == "option_map" and origin == "never imported")
)


#: #1511's class through a match: a module generic matching on its argument,
#: called from the entry at a type the module does not import.  The second
#: program adds a module that does import the type.
_COLOUR_SHARED = {
    "gboxb.vera": 'module gboxb;\n\npublic data GBox<T> {\n  GMk(T)\n}\n',
    "mb.vera": 'module mb;\n\npublic data Colour {\n  Red,\n  Green\n}\n',
    "ga.vera": (
        'module ga;\n'
        '\n'
        'import gboxb(GBox);\n'
        '\n'
        'public forall<T> fn gcount(@GBox<T> -> @Int)\n'
        '  requires(true)\n'
        '  ensures(@Int.result == 1)\n'
        '  effects(pure)\n'
        '{\n'
        '  match @GBox<T>.0 {\n'
        '    GMk(@T) -> 1\n'
        '  }\n'
        '}\n'
        '\n'
        'public forall<T> fn gget(@GBox<T> -> @T)\n'
        '  requires(true)\n'
        '  ensures(true)\n'
        '  effects(pure)\n'
        '{\n'
        '  match @GBox<T>.0 {\n'
        '    GMk(@T) -> @T.0\n'
        '  }\n'
        '}\n'
    ),
}
_COLOUR_MIN = {**_COLOUR_SHARED, "main.vera": (
    'import ga(gcount);\n'
    'import gboxb(GBox);\n'
    'import mb(Colour);\n'
    '\n'
    'public fn main(@Unit -> @Int)\n'
    '  requires(true)\n'
    '  ensures(true)\n'
    '  effects(pure)\n'
    '{\n'
    '  gcount(GMk(Green))\n'
    '}\n'
)}
_COLOUR_ARG_CTL = {
    **_COLOUR_SHARED,
    "ma.vera": (
        'module ma;\n'
        '\n'
        'import mb(Colour);\n'
        '\n'
        'public fn paint(@Colour -> @Int)\n'
        '  requires(true)\n'
        '  ensures(true)\n'
        '  effects(pure)\n'
        '{\n'
        '  match @Colour.0 {\n'
        '    Red -> 1,\n'
        '    Green -> 2\n'
        '  }\n'
        '}\n'
        '\n'
        'public fn pick(@Int -> @Colour)\n'
        '  requires(true)\n'
        '  ensures(true)\n'
        '  effects(pure)\n'
        '{\n'
        '  if @Int.0 == 0 then {\n'
        '    Red\n'
        '  } else {\n'
        '    Green\n'
        '  }\n'
        '}\n'
        '\n'
        'public fn count(@Array<Colour> -> @Int)\n'
        '  requires(true)\n'
        '  ensures(true)\n'
        '  effects(pure)\n'
        '{\n'
        '  array_length(@Array<Colour>.0)\n'
        '}\n'
    ),
    "main.vera": (
        'import ga(gcount, gget);\n'
        'import gboxb(GBox);\n'
        'import mb(Colour);\n'
        'import ma(paint);\n'
        '\n'
        'public fn main(@Unit -> @Int)\n'
        '  requires(true)\n'
        '  ensures(true)\n'
        '  effects(pure)\n'
        '{\n'
        '  gcount(GMk(Green)) + paint(Green)\n'
        '}\n'
    ),
}


class TestGenericsAtAnotherNamespacesType:
    """(f), continued: the type argument's namespace is a third one.

    The declaring namespace (the prelude, a library module, or the
    instantiating file itself) holds the type neither as its own nor as an
    import, and neither need the instantiating namespace: a value of a type
    a module declares reaches it through that module's functions.  Every
    one of these was skipped with E604 at the release branch's head, the
    instantiating file's own generic included (#1511).
    """

    @pytest.mark.parametrize("cell", TYPE_ORIGIN_CELLS, ids=lambda c: c.label)
    def test_compiles_and_runs(
        self, cell: TypeOriginCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 4)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert emitted, "no specialisation emitted: the cell is vacuous"
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")


    @pytest.mark.parametrize(("files", "value"), [
        pytest.param(_COLOUR_MIN, 1, id="the-entry-imports-the-type"),
        pytest.param(_COLOUR_ARG_CTL, 3,
                     id="and-a-module-that-imports-it-too"),
    ])
    def test_a_module_generic_matching_on_its_argument(
        self, files: dict[str, str], value: int, tmp_path: Path,
    ) -> None:
        """``ga``'s generic matches on a ``GBox<T>`` and is called from the
        entry at ``Colour``, a type ``ga`` does not import.  ``main``
        (6dc41d40) prints the value; the release branch (cc61fb9c) skipped
        ``gcount$Colour`` (E602) and dropped ``main`` (E620)."""
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", value)


#: A `data` type named like each built-in container, and a value of that
#: container's own type.  The declaration is refused at check (E158, #1547),
#: so only the control place compiles.
_CONTAINER_DECLS: dict[str, tuple[str, str, str, str]] = {
    # (declaration, a container value, its size)
    "Array": ("data Array {\n  MkArr(Int)\n}\n\n", "[1, 2, 3]",
              "array_length"),
    "Map": ("data Map {\n  MkMap(Int)\n}\n\n",
            'map_insert(map_insert(map_new(), "a", 1), "b", 2)', "map_size"),
    "Set": ("data Set {\n  MkSet(Int)\n}\n\n",
            "set_add(set_add(set_new(), 1), 2)", "set_size"),
}

#: Where the same-named data type is declared: the entry's own, a module's
#: the entry imports only a function from, or nowhere (the control, and the
#: bare `Map` / `Set` a clone is named after, #772).
CONTAINER_PLACES = ("entry declares it", "an imported module declares it",
                    "nothing declares it")

#: The generic the container value passes through, over `{C}` (the value),
#: wrapped by the container's size function.
_CONTAINER_GENERICS: dict[str, str] = {
    "option_unwrap_or": "option_unwrap_or(Some({C}), {C})",
    "option_unwrap_or, None": "option_unwrap_or(None, {C})",
    "result_unwrap_or": "result_unwrap_or(Ok({C}), {C})",
    "a module generic's own container parameter": "gl::sizeg({C})",
    "a module generic returning its argument": "gl::idg({C})",
}


@dataclass(frozen=True)
class ContainerCell:
    """A container value through a generic declared elsewhere, in a program
    that also declares a data type of the container's name."""

    container: str
    generic: str
    place: str

    @property
    def label(self) -> str:
        return f"{self.container}|{self.place}|{self.generic}"

    @property
    def value(self) -> int:
        return 2 if self.container != "Array" else 3

    def files(self) -> dict[str, str]:
        decl, value, size = _CONTAINER_DECLS[self.container]
        template = _CONTAINER_GENERICS[self.generic]
        if "sizeg" in template:
            # The module generic spells the container itself: its own
            # `Array<T>` parameter is the container whatever the entry
            # declares.
            expr = template.replace("{C}", value)
        else:
            expr = size + "(" + template.replace("{C}", value) + ")"
        gl = (_GL + "public forall<T> fn sizeg(@" + self.container
              + ("<T>" if self.container != "Map" else "<T, Int>")
              + " -> @Int)\n" + _NC + "{\n  " + size + "(@"
              + self.container
              + ("<T>" if self.container != "Map" else "<T, Int>")
              + ".0)\n}\n")
        probe = ("public fn probe(@Unit -> @Int)\n" + _NC + "{\n  " + expr
                 + " + one(0)\n}\n")
        files = {"gl.vera": gl}
        if self.place == "nothing declares it":
            decl = ""
        if self.place != "an imported module declares it":
            one = ("private fn one(@Int -> @Int)\n" + _NC
                   + "{\n  @Int.0\n}\n\n")
            files["main.vera"] = ("import gl;\n\n"
                                  + ("private " + decl if decl else "") + one
                                  + probe + "\n" + _NEST_MAIN)
        else:
            files["mh.vera"] = (
                "module mh;\n\npublic " + decl + "public fn one(@Int -> @Int)\n"
                + _NC + "{\n  @Int.0\n}\n")
            files["main.vera"] = ("import gl;\nimport mh(one);\n\n" + probe
                                  + "\n" + _NEST_MAIN)
        return files


CONTAINER_CELLS: tuple[ContainerCell, ...] = tuple(
    ContainerCell(container, generic, place)
    for container in _CONTAINER_DECLS
    for generic in _CONTAINER_GENERICS
    for place in CONTAINER_PLACES
)


class TestAContainerNamedDataType:
    """(f), continued: a clone's measurement admits the data types its type
    ARGUMENTS name, and nothing its generic's own declaration writes (PR
    #1508 review).

    Admitting every name a clone spelled let a `data Array` anywhere in the
    program re-type the prelude's own `Array<T>`, or a module generic's, as
    a one-word pointer: `array_length(option_unwrap_or(Some([1, 2]), []))`
    returned 0, and a module generic over `@Array<T>` built a module that
    fails to load.  A container's name in a type argument keeps the
    container's reading, since a clone is named after a container's bare
    head (#772) and the argument cannot say whose `Array` it is.

    A declaration of a container's name is now refused at check (E158,
    #1547), in the entry and in a module alike, so those places are
    refusal cells; the place that declares nothing still runs.
    """

    @pytest.mark.parametrize("cell", CONTAINER_CELLS, ids=lambda c: c.label)
    def test_the_container_keeps_its_representation(
        self, cell: ContainerCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        if cell.place != "nothing declares it":
            assert [d.error_code for d in outcome.check_errors] == ["E158"], (
                outcome.describe())
            return
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert emitted, "no specialisation emitted: the cell is vacuous"
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    def test_a_user_type_as_a_type_argument_still_compiles(
        self, tmp_path: Path,
    ) -> None:
        """The admission itself: a type argument naming the entry's own data
        type is a member of the prelude's namespace while the clone is
        measured (#1511), so the value keeps its one-word pointer."""
        main = ("private data Shape {\n  Sq(Int)\n}\n\n"
                "public fn main(@Unit -> @Int)\n" + _NC
                + "{\n  match option_unwrap_or(Some(Sq(5)), Sq(6)) {\n"
                "    Sq(@Int) -> @Int.0\n  }\n}\n")
        outcome = pipeline(tmp_path, {"main.vera": main})
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 5)

    @pytest.mark.parametrize("call", ("gl::wrapg(Sq(5))", "gl::idg(Sq(5))",
                                      "gl::viag(Sq(5))", "gl::outerg(Sq(5))"))
    def test_a_clone_and_its_hoisted_helper_at_a_user_type(
        self, call: str, tmp_path: Path,
    ) -> None:
        """The arguments reach every declaration a clone becomes: a module
        generic's `where` helper, hoisted per clone, is measured at the
        entry's `Shape` too, and so is a module generic the entry's own
        `idg` shadows, reached qualified under its `mod$` symbol."""
        gl = (_GL + "public forall<T> fn wrapg(@T -> @T)\n" + _NC
              + "{\n  inner(@T.0)\n}\nwhere {\n  fn inner(@T -> @T)\n"
              "    requires(true)\n    ensures(true)\n    effects(pure)\n"
              "  {\n    @T.0\n  }\n}\n\n"
              # reached qualified only (the entry shadows it), and calling a
              # generic the entry does not: its clone is chased from there
              "public forall<T> fn viag(@T -> @T)\n" + _NC
              + "{\n  wrapg(@T.0)\n}\n\n"
              # a generic helper under a generic
              "public forall<T> fn outerg(@T -> @T)\n" + _NC
              + "{\n  innerg(@T.0)\n}\nwhere {\n  forall<U> fn innerg(@U -> @U)\n"
              "    requires(true)\n    ensures(true)\n    effects(pure)\n"
              "  {\n    @U.0\n  }\n}\n")
        main = ("import gl;\n\nprivate data Shape {\n  Sq(Int)\n}\n\n"
                + _USER_GENERICS["idg"]
                + _USER_GENERICS["idg"].replace("idg", "viag")
                + "public fn main(@Unit -> @Int)\n" + _NC
                + "{\n  let @Int = match " + call
                + " {\n    Sq(@Int) -> @Int.0\n  };\n  @Int.0 + idg(0) + viag(0)\n}\n")
        outcome = pipeline(tmp_path, {"gl.vera": gl, "main.vera": main})
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 5)

    def test_a_container_named_data_type_as_a_type_argument(
        self, tmp_path: Path,
    ) -> None:
        """The other reading of the same spelling: the entry's own
        `data Array` passed through the prelude's generic.  The argument is
        `Array` whichever type it is, and the prelude reads the container
        (#1519's mechanism), so the declaration is refused at check instead
        (E158, #1547)."""
        main = ("private data Array {\n  MkArr(Int)\n}\n\n"
                "public fn main(@Unit -> @Int)\n" + _NC
                + "{\n  match option_unwrap_or(Some(MkArr(5)), MkArr(6)) {\n"
                "    MkArr(@Int) -> @Int.0\n  }\n}\n")
        outcome = pipeline(tmp_path, {"main.vera": main})
        assert [d.error_code for d in outcome.check_errors] == ["E158"], (
            outcome.describe())


# =====================================================================
# (g) Generics instantiated at a type alias (#1511)
# =====================================================================
#
# A type argument is written in the namespace that instantiates a generic,
# and the clone is measured in the namespace that declared it.  Named by the
# raw alias, the clone read `@Num` where `Num` means nothing (the prelude, a
# library module) or something else, and was skipped (E604) or built into a
# module that fails to load.  The argument is now resolved where it was
# written (`vera.monomorphize.canonical_type_arg`), by discovery and by the
# call site alike.

#: (declaration, the value to bind, how the probe turns a value into Int)
_ALIASES: dict[str, tuple[str, str, str]] = {
    "plain": ("type Num = Int;\n\n", "5", "{E}"),
    "refined": ("type Num = { @Int | @Int.0 > 0 };\n\n", "5", "{E}"),
    "String": ("type Num = String;\n\n", '"abcde"', "string_length({E})"),
    "alias of an alias": ("type Base = Int;\n\ntype Num = Base;\n\n", "5",
                          "{E}"),
}

#: The generic, by where it is declared, over `{X}` (a `Num`) and `{D}`
#: (another value of the type).
_ALIAS_GENERICS: dict[str, tuple[str, str]] = {
    "prelude": ("", "option_unwrap_or(Some({X}), {D})"),
    "own generic": ("idg", "idg({X})"),
    "library generic": ("gl", "gl::idg({X})"),
    "imported generic": ("gl(idg)", "idg({X})"),
    "nested in a constructor argument": (
        "idg", "option_unwrap_or(Some(idg({X})), {D})"),
}


@dataclass(frozen=True)
class AliasCell:
    """A generic instantiated at an alias declared where the call is."""

    alias: str
    generic: str
    place: str          # "entry" or "module"

    @property
    def label(self) -> str:
        return f"{self.place}|{self.alias}|{self.generic}"

    @property
    def value(self) -> int:
        return 5

    def files(self) -> dict[str, str]:
        decl, value, wrap = _ALIASES[self.alias]
        needs, template = _ALIAS_GENERICS[self.generic]
        expr = template.replace("{X}", "@Num.0").replace("{D}", "@Num.0")
        own = _USER_GENERICS["idg"] if needs == "idg" else ""
        imports = f"import {needs};\n\n" if needs.startswith("gl") else ""
        body = (imports + decl + own + "public fn probe(@Unit -> @Int)\n"
                + _NC + "{\n  let @Num = " + value + ";\n  "
                + wrap.replace("{E}", expr) + "\n}\n")
        files = {"gl.vera": _GL} if imports else {}
        if self.place == "entry":
            files["main.vera"] = body + "\n" + _NEST_MAIN
        else:
            files["mb.vera"] = "module mb;\n\n" + body
            files["main.vera"] = "import mb(probe);\n\n" + _NEST_MAIN
        return files


ALIAS_CELLS: tuple[AliasCell, ...] = tuple(
    AliasCell(alias, generic, place)
    for alias in _ALIASES
    for generic in _ALIAS_GENERICS
    for place in ("entry", "module")
)

#: The alias names a type the declaring module declares as data: the
#: argument is the caller's, so the module's `Shape` is never consulted.
_CAPTURE_GL = (
    _GL.rstrip("\n") + "\n\npublic data Shape {\n  Sq(Int)\n}\n"
)


class TestGenericsAtATypeAlias:
    """(g): a generic compiles at a type alias of the instantiating
    namespace, wherever the generic is declared (#1511)."""

    @pytest.mark.parametrize("cell", ALIAS_CELLS, ids=lambda c: c.label)
    def test_compiles_and_runs(
        self, cell: AliasCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert emitted, "no specialisation emitted: the cell is vacuous"
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")
        # Named by what the alias MEANS, never by the alias.
        assert not any("Num" in "".join(types) or "Base" in "".join(types)
                       for _name, types in emitted), sorted(emitted)

    @pytest.mark.parametrize("place", ("entry", "module"))
    def test_an_alias_named_like_the_declaring_modules_data_type(
        self, place: str, tmp_path: Path,
    ) -> None:
        """The caller's `type Shape = Int;` against `gl`'s `data Shape`:
        the argument is resolved where it is written, so the clone is
        `idg$Int`, and `gl`'s `Shape` is never consulted."""
        body = ("import gl(idg);\n\ntype Shape = Int;\n\n"
                "public fn probe(@Unit -> @Int)\n" + _NC
                + "{\n  let @Shape = 7;\n  idg(@Shape.0)\n}\n")
        files = {"gl.vera": _CAPTURE_GL}
        if place == "entry":
            files["main.vera"] = body + "\n" + _NEST_MAIN
        else:
            files["mb.vera"] = "module mb;\n\n" + body
            files["main.vera"] = "import mb(probe);\n\n" + _NEST_MAIN
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 7)

    @pytest.mark.xfail(strict=True, reason=(
        "#1519: the substituted data type `Shape` reads as the declaring "
        "module's alias of `Int` inside the clone"))
    @pytest.mark.parametrize("call", ("idg(Circle(4))", "gl::idg(Circle(4))"))
    def test_a_data_type_named_like_the_declaring_modules_alias(
        self, call: str, tmp_path: Path,
    ) -> None:
        """The other direction: `gl` declares `type Shape = Int;`, and the
        entry calls `gl`'s generic at its own `data Shape`.  The clone is
        rightly keyed on the entry's type, and is then built into a module
        that fails to load (#1519, on `main` as well)."""
        gl = (_GL.rstrip("\n") + "\n\ntype Shape = Int;\n\n"
              "public fn seven(@Unit -> @Int)\n" + _NC
              + "{\n  let @Shape = 7;\n  @Shape.0\n}\n")
        imports = "import gl(idg);\n" if call.startswith("idg") else (
            "import gl;\n")
        main = (imports + "\nprivate data Shape {\n  Circle(Int),\n"
                "  Square(Int)\n}\n\npublic fn main(@Unit -> @Int)\n" + _NC
                + "{\n  match " + call + " {\n    Circle(@Int) -> @Int.0,\n"
                "    Square(@Int) -> @Int.0 * 10\n  }\n}\n")
        outcome = pipeline(tmp_path, {"gl.vera": gl, "main.vera": main})
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 4)

    def test_no_prelude_body_writes_a_type_argument(self) -> None:
        """Discovery walks the prelude's bodies in the entry file's
        namespace, which is only safe while no prelude body calls a
        generic: a type argument written there would be resolved against
        the entry's aliases.  If this fails, give the prelude its own
        scope in `canonical_type_args`."""
        generics = prelude_generics()
        from vera.prelude import inject_prelude

        program = parse_to_ast(
            "public fn main(@Unit -> @Int)\n" + _NC + "{\n  1\n}\n")
        inject_prelude(program)
        called: set[str] = set()

        def walk(node: object) -> None:
            if isinstance(node, (ast.FnCall, ast.ModuleCall)):
                called.add(node.name)
            if isinstance(node, ast.Node):
                for f in dataclasses.fields(node):
                    walk(getattr(node, f.name))
            elif isinstance(node, (list, tuple)):
                for item in node:
                    walk(item)

        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name != "main":
                walk(tld.decl.body)
        assert not called & set(generics), sorted(called & set(generics))


class TestQualifiedCallsNameTheirOwnTarget:
    """(e), continued: two cases from the review of the #1509 fix.

    A qualified call is named from the declaration it reaches, and the
    qualified-only discovery reads the names its module can see."""

    def test_a_non_generic_target_beside_a_local_generic(
        self, tmp_path: Path,
    ) -> None:
        """`m::foo` is a non-generic module function; the entry declares a
        generic `foo` of its own.  Discovery named `idg`'s argument from the
        entry's generic (`Option`) where the call site names the module's
        function's return (`Int`)."""
        files = {
            "m.vera": ("module m;\n\npublic fn foo(@Int -> @Int)\n" + _NC
                       + "{\n  @Int.0 + 1\n}\n"),
            "main.vera": (
                "import m;\n\n"
                "private forall<T> fn foo(@T -> @Option<T>)\n" + _NC
                + "{\n  Some(@T.0)\n}\n\n" + _USER_GENERICS["idg"]
                + "public fn main(@Unit -> @Int)\n" + _NC
                + "{\n  idg(m::foo(3)) + option_unwrap_or(foo(1), 0)\n}\n"),
        }
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 5)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", files)
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    @pytest.mark.parametrize("call", ("idg(get(()))", "get(()) |> idg()"))
    def test_an_operation_in_a_module_private_generics_argument(
        self, call: str, tmp_path: Path,
    ) -> None:
        """Inside a module, `get(())` under the module's own `State<Int>`
        handler is the operation, though the ENTRY declares a function
        `get`.  The qualified-only discovery for the module's private
        generic read the flat table, took the entry's `get`, and named a
        clone the call site does not call.  The piped spelling walks the
        desugared call, in the same namespace (PR #1508 review)."""
        files = {
            "mb.vera": (
                "module mb;\n\n" + _USER_GENERICS["idg"]
                + "public fn probe(@Unit -> @Int)\n" + _NC
                + "{\n  handle[State<Int>](@Int = 42) {\n"
                "    get(@Unit) -> { resume(@Int.0) },\n"
                "    put(@Int) -> { resume(()) }\n"
                f"  }} in {{\n    {call}\n  }}\n}}\n"),
            "main.vera": (
                "import mb(probe);\n\n"
                "private fn get(@Unit -> @Bool)\n" + _NC + "{\n  true\n}\n\n"
                "public fn main(@Unit -> @Int)\n" + _NC
                + "{\n  if get(()) then { probe(()) } else { 0 }\n}\n"),
        }
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 42)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", files)
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")


# =====================================================================
# (h) A module's own function under a name the entry also declares
# =====================================================================
#
# Code generation has one flat function namespace, where the ENTRY's
# declaration holds a bare name, so a module's own function of that name is
# emitted under `mod$<path>$name`.  A bare call in the module's bodies means
# the module's function (§8.5.2), and only its target was redirected: its
# type was named from the entry's declaration, so a generic called on the
# result was specialised at the entry's type, and beside an entry GENERIC of
# the name the generic rewrite took the call itself (PR #1508 review).  Each
# cell runs to its value and holds against the verifier's discovery.

#: The entry's own declaration of `foo`, and what `main` adds for it.
_ENTRY_FOO: dict[str, tuple[str, str]] = {
    "an entry generic": (
        "private forall<T> fn foo(@T -> @T)\n" + _NC + "{\n  @T.0\n}\n\n",
        " + foo(0)"),
    "an entry function": (
        "private fn foo(@Int -> @Int)\n" + _NC + "{\n  @Int.0 + 10\n}\n\n",
        " + foo(0)"),
    "nothing in the entry": ("", ""),
}

#: `bar`'s body over `{F}`, the module's call `foo(@Int.0)` (a `Bool`).  The
#: module's `foo` is false at 1, so `bar(1)` is 2: a call that reaches the
#: entry's `foo` instead yields a nonzero `Int`, which reads as `true` (1)
#: where the module still loads, and 2 cannot coincide with it.
_FOO_POSITIONS: dict[str, str] = {
    "a private generic's argument": "if idm({F}) then { 1 } else { 2 }",
    "a prelude generic's argument":
        "if option_unwrap_or(Some({F}), false) then { 1 } else { 2 }",
    "a library generic's argument, qualified":
        "if gl::idg({F}) then { 1 } else { 2 }",
    "a constructor argument":
        "match Some({F}) {\n    Some(@Bool) -> if @Bool.0 then { 1 } "
        "else { 2 },\n    None -> 3\n  }",
    "a let binding": "let @Bool = {F};\n  if @Bool.0 then { 1 } else { 2 }",
    "a condition": "if {F} then { 1 } else { 2 }",
    "piped": "if @Int.0 |> foo() then { 1 } else { 2 }",
    "nested in two generics": "if idm(idm({F})) then { 1 } else { 2 }",
    "an array element":
        "let @Array<Bool> = [{F}];\n  if @Array<Bool>.0[0] then { 1 } else { 2 }",
    "a closure body":
        "if option_unwrap_or(option_map(Some(@Int.0), fn(@Int -> @Bool) "
        "effects(pure) { {F} }), false) then { 1 } else { 2 }",
}


def _callers_of_the_entrys_foo(wat: str) -> set[str]:
    """Every emitted function but `main` that calls the entry's `foo`.

    The entry's `foo` is `$foo`, or a clone `$foo$…` of it; a module's
    `foo` the entry displaces is `$mod$<path>$foo`.  Only `main` calls the
    entry's.  A `Bool` read of the wrong call's result can still land on
    the right answer (an `Int` payload read at a `Bool`'s offset is zero),
    so each cell asserts the call's target as well as its value.
    """
    callers: set[str] = set()
    for chunk in re.split(r"^  \(func ", wat, flags=re.M)[1:]:
        name = chunk.split(None, 1)[0].lstrip("$")
        if name != "main" and re.search(
                r"\bcall \$foo(?:\$[^\s)]*)?(?=[\s)])", chunk):
            callers.add(name)
    return callers


@dataclass(frozen=True)
class DisplacedCell:
    entry: str
    visibility: str     # the module's `foo`
    position: str

    @property
    def label(self) -> str:
        return f"{self.entry}|{self.visibility}|{self.position}"

    @property
    def value(self) -> int:
        return 12 if self.entry == "an entry function" else 2

    def files(self) -> dict[str, str]:
        decl, call = _ENTRY_FOO[self.entry]
        body = _FOO_POSITIONS[self.position].replace("{F}", "foo(@Int.0)")
        ma = ("module ma;\n\nimport gl;\n\n" + self.visibility
              + " fn foo(@Int -> @Bool)\n" + _NC + "{\n  @Int.0 > 5\n}\n\n"
              + "private forall<T> fn idm(@T -> @T)\n" + _NC
              + "{\n  @T.0\n}\n\npublic fn bar(@Int -> @Int)\n" + _NC
              + "{\n  " + body + "\n}\n")
        main = ("import ma(bar);\n\n" + decl + "public fn main(@Unit -> @Int)\n"
                + _NC + "{\n  bar(1)" + call + "\n}\n")
        return {"gl.vera": _GL, "ma.vera": ma, "main.vera": main}


DISPLACED_CELLS: tuple[DisplacedCell, ...] = tuple(
    DisplacedCell(entry, visibility, position)
    for entry in _ENTRY_FOO
    for visibility in ("private", "public")
    for position in _FOO_POSITIONS
)


class TestAModulesFunctionTheEntryDisplaces:
    """(h): a module's bare call to its own function means that function,
    whatever the entry declares under the name."""

    @pytest.mark.parametrize("cell", DISPLACED_CELLS, ids=lambda c: c.label)
    def test_the_module_calls_its_own_function(
        self, cell: DisplacedCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        assert outcome.result is not None
        if cell.entry != "nothing in the entry":
            assert not _callers_of_the_entrys_foo(outcome.result.wat)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    def test_a_parameterised_result_names_the_same_clone_on_both_sides(
        self, tmp_path: Path,
    ) -> None:
        """The module's `foo` returns `Option<Int>`: discovery must name
        `idm`'s argument from the module's declaration as the call site
        does (`Option`, #772), not from the checker's full type."""
        files = DisplacedCell(
            "an entry generic", "private", "a private generic's argument",
        ).files()
        files["ma.vera"] = files["ma.vera"].replace(
            "fn foo(@Int -> @Bool)", "fn foo(@Int -> @Option<Int>)").replace(
            "@Int.0 > 5\n}", "Some(@Int.0)\n}").replace(
            "if idm(foo(@Int.0)) then { 1 } else { 2 }",
            "option_unwrap_or(idm(foo(@Int.0)), 7)")
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 1)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", files)
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    def test_a_where_helper_of_the_name_owns_the_call(
        self, tmp_path: Path,
    ) -> None:
        """The rename is shadow-aware: inside `bar`, whose `where` helper is
        also `foo`, the bare call is the helper's (1 > 0, so 1), not the
        module's top-level `foo` (1 > 5 is false, which would give 2).  The
        run only: the verifier's discovery names the helper's call from the
        entry's generic, as it did before this change."""
        files = DisplacedCell(
            "an entry generic", "private", "a private generic's argument",
        ).files()
        files["ma.vera"] = files["ma.vera"].rstrip("\n") + (
            "\nwhere {\n  fn foo(@Int -> @Bool)\n    requires(true)\n"
            "    ensures(true)\n    effects(pure)\n  {\n    @Int.0 > 0\n  }\n}\n")
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 1)


# =====================================================================
# (h), imported: a function the module imports, under a name the entry
# also declares
# =====================================================================
#
# The same flat namespace, and a module's bare call that means a function
# the module IMPORTED (§8.5.2).  Its own module emits that function under
# `mod$<path>$name` while the entry holds the bare name, and §8.9.1 says a
# call from another module's body is compiled to that name too.  It was
# compiled against the ENTRY's declaration instead: the entry's function
# beside a non-generic one, a silent wrong value, and beside a generic one
# its clone, a module that fails to load (PR #1508 review).  Each cell runs
# to its value and holds against the verifier's discovery.

#: `ma`'s `foo`, and how `mb` imports it.  An imported generic reaches the
#: same rule by #1274's reroute, and stands beside the functions as the
#: control that the class is the name, not the genericity.
_IMPORTED_FOO: dict[str, tuple[str, str]] = {
    "a function, imported by name": (
        "public fn foo(@Int -> @Bool)\n" + _NC + "{\n  @Int.0 > 5\n}\n",
        "import ma(foo);\n"),
    "a function, imported by wildcard": (
        "public fn foo(@Int -> @Bool)\n" + _NC + "{\n  @Int.0 > 5\n}\n",
        "import ma;\n"),
    "a generic, imported by name": (
        "public forall<T> fn foo(@T -> @Bool)\n" + _NC + "{\n  false\n}\n",
        "import ma(foo);\n"),
}


def _importing_module(imp: str, bar: str) -> str:
    """`mb`: imports `foo` by *imp*, and declares `idm` and *bar*."""
    return ("module mb;\n\nimport gl;\n" + imp + "\n"
            + "private forall<T> fn idm(@T -> @T)\n" + _NC
            + "{\n  @T.0\n}\n\n" + bar)


@dataclass(frozen=True)
class ImportedDisplacedCell:
    entry: str
    supplier: str       # `ma`'s `foo`, and `mb`'s import of it
    position: str

    @property
    def label(self) -> str:
        return f"{self.entry}|{self.supplier}|{self.position}"

    @property
    def value(self) -> int:
        return 12 if self.entry == "an entry function" else 2

    def files(self) -> dict[str, str]:
        decl, call = _ENTRY_FOO[self.entry]
        foo, imp = _IMPORTED_FOO[self.supplier]
        body = _FOO_POSITIONS[self.position].replace("{F}", "foo(@Int.0)")
        bar = ("public fn bar(@Int -> @Int)\n" + _NC
               + "{\n  " + body + "\n}\n")
        main = ("import mb(bar);\n\n" + decl + "public fn main(@Unit -> @Int)\n"
                + _NC + "{\n  bar(1)" + call + "\n}\n")
        return {"gl.vera": _GL, "ma.vera": "module ma;\n\n" + foo,
                "mb.vera": _importing_module(imp, bar), "main.vera": main}


IMPORTED_DISPLACED_CELLS: tuple[ImportedDisplacedCell, ...] = tuple(
    ImportedDisplacedCell(entry, supplier, position)
    for entry in _ENTRY_FOO
    for supplier in _IMPORTED_FOO
    for position in _FOO_POSITIONS
)

#: The silent half.  `ma`'s `foo` adds 100, which neither of the entry's
#: `foo`s does, so a call that reaches the entry's declaration is a wrong
#: value rather than a module that fails to load, and `bar`'s `ensures`,
#: which the verifier proves from `ma`'s contract, fails when it runs.
_INT_FOO = ("public fn foo(@Int -> @Int)\n  requires(true)\n"
            "  ensures(@Int.result == @Int.0 + 100)\n  effects(pure)\n"
            "{\n  @Int.0 + 100\n}\n")

#: `bar`'s body over the call in each of `_FOO_POSITIONS`' positions, and
#: bare, each computing `@Int.0 + 100`.
_INT_POSITIONS: dict[str, str] = {
    "a bare call": "{F}",
    "a private generic's argument": "idm({F})",
    "a prelude generic's argument": "option_unwrap_or(Some({F}), 0)",
    "a library generic's argument, qualified": "gl::idg({F})",
    "a constructor argument":
        "match Some({F}) {\n    Some(@Int) -> @Int.0,\n    None -> 0\n  }",
    "a let binding": "let @Int = {F};\n  @Int.0",
    "a condition": "if {F} > 100 then { @Int.0 + 100 } else { 0 }",
    "piped": "@Int.0 |> foo()",
    "nested in two generics": "idm(idm({F}))",
    "an array element": "let @Array<Int> = [{F}];\n  @Array<Int>.0[0]",
    "a closure body":
        "option_unwrap_or(option_map(Some(@Int.0), fn(@Int -> @Int) "
        "effects(pure) { {F} }), 0)",
}


@dataclass(frozen=True)
class ImportedValueCell:
    entry: str
    imp: str            # `mb`'s import of `ma`
    position: str

    @property
    def label(self) -> str:
        return f"{self.entry}|{self.imp.strip()}|{self.position}"

    @property
    def value(self) -> int:
        """`bar(1)` is 101; `main` adds the entry's `foo(0)`: 0 or 10."""
        return 111 if self.entry == "an entry function" else 101

    def files(self) -> dict[str, str]:
        decl, call = _ENTRY_FOO[self.entry]
        bar = ("public fn bar(@Int -> @Int)\n  requires(true)\n"
               "  ensures(@Int.result == @Int.0 + 100)\n  effects(pure)\n"
               "{\n  " + _INT_POSITIONS[self.position].replace(
                   "{F}", "foo(@Int.0)") + "\n}\n")
        main = ("import mb(bar);\n\n" + decl + "public fn main(@Unit -> @Int)\n"
                + _NC + "{\n  bar(1)" + call + "\n}\n")
        return {"gl.vera": _GL, "ma.vera": "module ma;\n\n" + _INT_FOO,
                "mb.vera": _importing_module(self.imp, bar),
                "main.vera": main}


IMPORTED_VALUE_CELLS: tuple[ImportedValueCell, ...] = tuple(
    ImportedValueCell(entry, imp, position)
    for entry in _ENTRY_FOO
    for imp in ("import ma(foo);\n", "import ma;\n")
    for position in _INT_POSITIONS
)


class TestAFunctionTheModuleImportsTheEntryDisplaces:
    """(h), imported: a module's bare call to a function it imports means
    that function, whatever the entry declares under the name."""

    def test_both_halves_hold_the_call_in_every_position(self) -> None:
        """The value half covers every position the `Bool` half does, and
        the bare call besides."""
        assert set(_INT_POSITIONS) == set(_FOO_POSITIONS) | {"a bare call"}

    @pytest.mark.parametrize(
        "cell", IMPORTED_DISPLACED_CELLS, ids=lambda c: c.label)
    def test_the_module_calls_the_function_it_imports(
        self, cell: ImportedDisplacedCell, tmp_path: Path,
    ) -> None:
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        assert outcome.result is not None
        if cell.entry != "nothing in the entry":
            assert not _callers_of_the_entrys_foo(outcome.result.wat)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    @pytest.mark.parametrize(
        "cell", IMPORTED_VALUE_CELLS, ids=lambda c: c.label)
    def test_the_value_is_the_imported_functions(
        self, cell: ImportedValueCell, tmp_path: Path,
    ) -> None:
        """101 from `bar(1)`, never the entry's 1 or 11, and `bar`'s
        postcondition holds when it runs, as the verifier proves it."""
        outcome = pipeline(tmp_path, cell.files())
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", cell.value)
        assert outcome.result is not None
        if cell.entry != "nothing in the entry":
            assert not _callers_of_the_entrys_foo(outcome.result.wat)
        emitted, discovered = _emitted_and_discovered(
            tmp_path / "differential", cell.files())
        assert not uncovered_instances(emitted, discovered), (
            f"emitted {sorted(emitted)}, discovered {sorted(discovered)}")

    def test_the_module_function_under_the_name_is_its_own(
        self, tmp_path: Path,
    ) -> None:
        """The module's own declaration shadows its import (§8.5.2): with a
        wildcard import of `ma` and its own `foo` (1 > 0, so 1), `bar` calls
        its own, not the import (1 > 5 is false, which would give 2)."""
        files = ImportedDisplacedCell(
            "an entry generic", "a function, imported by wildcard",
            "a condition").files()
        files["mb.vera"] = files["mb.vera"].replace(
            "public fn bar(", "private fn foo(@Int -> @Bool)\n" + _NC
            + "{\n  @Int.0 > 0\n}\n\npublic fn bar(")
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 1)

    @pytest.mark.parametrize(("mc_foo", "mc_import"), [
        pytest.param("public", "import mc(other);\n",
                     id="outside-the-import-filter"),
        pytest.param("private", "import mc;\n", id="private"),
    ])
    def test_a_foo_the_module_cannot_name_supplies_nothing(
        self, mc_foo: str, mc_import: str, tmp_path: Path,
    ) -> None:
        """A second module `mc` declares a `foo` that `mb` cannot name:
        outside `mb`'s filter for `mc`, or private.  `mb`'s `foo` is still
        `ma`'s alone (1 > 5 is false, so 2), and a call counted to `mc`'s
        too would name no single function and reach the entry's."""
        files = ImportedDisplacedCell(
            "an entry generic", "a function, imported by name",
            "a condition").files()
        files["mc.vera"] = (
            "module mc;\n\n" + mc_foo + " fn foo(@Int -> @Bool)\n" + _NC
            + "{\n  @Int.0 > 0\n}\n\npublic fn other(@Int -> @Int)\n" + _NC
            + "{\n  if foo(@Int.0) then { 7 } else { 8 }\n}\n")
        files["mb.vera"] = files["mb.vera"].replace(
            "import ma(foo);\n", "import ma(foo);\n" + mc_import)
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 2)
        assert outcome.result is not None
        assert not _callers_of_the_entrys_foo(outcome.result.wat)

    def test_a_where_helper_of_the_name_owns_the_call(
        self, tmp_path: Path,
    ) -> None:
        """Shadow-aware as for the module's own function: inside `bar`,
        whose `where` helper is `foo`, the bare call is the helper's (1 > 0,
        so 1), not the imported `foo` (1 > 5 is false, which gives 2)."""
        files = ImportedDisplacedCell(
            "an entry generic", "a function, imported by name",
            "a private generic's argument").files()
        files["mb.vera"] = files["mb.vera"].rstrip("\n") + (
            "\nwhere {\n  fn foo(@Int -> @Bool)\n    requires(true)\n"
            "    ensures(true)\n    effects(pure)\n  {\n    @Int.0 > 0\n  }\n}\n")
        outcome = pipeline(tmp_path, files)
        assert outcome.accepted and outcome.compiles_clean, (
            outcome.describe())
        assert run_main(outcome) == ("ok", 1)
