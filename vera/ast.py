"""Vera AST node definitions.

Frozen dataclasses representing the typed abstract syntax tree.
Every node carries an optional source span for error reporting.
The hierarchy is shallow: Node → category base → concrete node.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass
from enum import Enum
from typing import Any


# =====================================================================
# Foundation
# =====================================================================

@dataclass(frozen=True)
class Span:
    """Source location span from Lark's propagated positions."""
    line: int
    column: int
    end_line: int
    end_column: int

    def __str__(self) -> str:
        return f"{self.line}:{self.column}-{self.end_line}:{self.end_column}"


def span_key(node: "Node") -> tuple[int, int, int, int] | None:
    """Canonical side-table key for an expression — its
    ``(line, column, end_line, end_column)`` span, or ``None`` if the node is
    unspanned.

    Single source of truth for the checker writers (``expr_types`` /
    ``expr_semantic_types`` / ``expr_target_types``) and the verifier reader
    (``_resolved_type_of`` / ``_target_type_of``): both halves of the #747
    side-table must agree on the key format, so neither hand-rolls the tuple
    (#759).
    """
    sp = getattr(node, "span", None)
    if sp is None:
        return None
    return (sp.line, sp.column, sp.end_line, sp.end_column)


@dataclass(frozen=True)
class Node:
    """Abstract base for all AST nodes."""
    span: Span | None = field(default=None, kw_only=True, repr=False, compare=False)

    def to_dict(self) -> dict[str, Any]:
        """Serialise to a JSON-compatible dict."""
        result: dict[str, Any] = {"_type": type(self).__name__}
        for f in fields(self):
            result[f.name] = _serialise(getattr(self, f.name))
        return result

    def pretty(self, indent: int = 0) -> str:
        """Human-readable indented text representation."""
        prefix = "  " * indent
        lines = [f"{prefix}{type(self).__name__}"]
        for f in fields(self):
            if f.name == "span":
                continue
            val = getattr(self, f.name)
            lines.extend(_pretty_field(f.name, val, indent + 1))
        return "\n".join(lines)


def _serialise(val: Any) -> Any:
    """Recursively convert a value for JSON serialisation."""
    if isinstance(val, Node):
        return val.to_dict()
    if isinstance(val, Span):
        # One span encoding for the whole JSON surface: `span` and
        # `where_span` must serialise identically, not one structured
        # and one as a display string.
        return {"line": val.line, "column": val.column,
                "end_line": val.end_line, "end_column": val.end_column}
    if isinstance(val, tuple):
        return [_serialise(v) for v in val]
    if isinstance(val, Enum):
        return val.value
    if val is None or isinstance(val, (str, int, float, bool)):
        return val
    return str(val)  # pragma: no cover


def _pretty_field(name: str, val: Any, indent: int) -> list[str]:
    """Format a single field for pretty-printing."""
    prefix = "  " * indent
    if val is None:
        return []
    if isinstance(val, Node):
        return [f"{prefix}{name}:", val.pretty(indent + 1)]
    if isinstance(val, tuple) and len(val) > 0 and isinstance(val[0], Node):
        lines = [f"{prefix}{name}:"]
        for item in val:
            lines.append(item.pretty(indent + 1))
        return lines
    if isinstance(val, tuple):
        items = ", ".join(str(v.value) if isinstance(v, Enum) else repr(v)
                         for v in val)
        return [f"{prefix}{name}: ({items})"]
    if isinstance(val, Enum):
        return [f"{prefix}{name}: {val.value}"]
    return [f"{prefix}{name}: {val!r}"]


# =====================================================================
# Enums
# =====================================================================

class BinOp(str, Enum):
    """Binary operator kinds."""
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"
    MOD = "%"
    EQ = "=="
    NEQ = "!="
    LT = "<"
    GT = ">"
    LE = "<="
    GE = ">="
    AND = "&&"
    OR = "||"
    IMPLIES = "==>"
    PIPE = "|>"


class UnaryOp(str, Enum):
    """Unary operator kinds."""
    NOT = "!"
    NEG = "-"


# =====================================================================
# Category Bases
# =====================================================================

@dataclass(frozen=True)
class Expr(Node):
    """Abstract base for all expression nodes."""


@dataclass(frozen=True)
class TypeExpr(Node):
    """Abstract base for all type expression nodes."""


@dataclass(frozen=True)
class Pattern(Node):
    """Abstract base for all pattern nodes."""


@dataclass(frozen=True)
class Stmt(Node):
    """Abstract base for all statement nodes."""


@dataclass(frozen=True)
class Decl(Node):
    """Abstract base for all declaration nodes."""


@dataclass(frozen=True)
class Contract(Node):
    """Abstract base for contract clauses."""


@dataclass(frozen=True)
class EffectRow(Node):
    """Abstract base for effect specifications."""


@dataclass(frozen=True)
class EffectRefNode(Node):
    """Abstract base for effect references."""


# =====================================================================
# Program Structure
# =====================================================================

@dataclass(frozen=True)
class Program(Node):
    """Root AST node — a complete Vera source file."""
    module: ModuleDecl | None
    imports: tuple[ImportDecl, ...]
    declarations: tuple[TopLevelDecl, ...]


@dataclass(frozen=True)
class ModuleDecl(Node):
    """Module declaration: module path.to.module;"""
    path: tuple[str, ...]


@dataclass(frozen=True)
class ImportDecl(Node):
    """Import declaration: import path.to.module(name1, name2);"""
    path: tuple[str, ...]
    names: tuple[str, ...] | None  # None = import everything


@dataclass(frozen=True)
class TopLevelDecl(Node):
    """A declaration with optional visibility modifier."""
    visibility: str | None  # "public" | "private" | None
    decl: Decl


# =====================================================================
# Declarations
# =====================================================================

@dataclass(frozen=True)
class FnDecl(Decl):
    """Function declaration with contracts, effects, and body."""
    name: str
    forall_vars: tuple[str, ...] | None
    forall_constraints: tuple[AbilityConstraint, ...] | None
    params: tuple[TypeExpr, ...]
    return_type: TypeExpr
    contracts: tuple[Contract, ...]
    effect: EffectRow
    body: Block
    where_fns: tuple[FnDecl, ...] | None
    # Annotation-comment labels (spec 1.3), positional so they survive
    # De Bruijn addressing: `param_annotations[i]` labels `params[i]`,
    # and an unlabelled slot holds None rather than being omitted —
    # collapsing the gaps would shift every later label onto the wrong
    # slot.  None (rather than a tuple of Nones) means the AST was built
    # without source, so nothing is known either way.
    param_annotations: tuple[str | None, ...] | None = None
    return_annotation: str | None = None
    # Source span of the `where { ... }` block, when there is one.  The
    # keyword has no node of its own — `where_fns` holds only the
    # functions inside — so a comment written above `where` has no
    # position after it to attach to and gets pulled into the block.
    # None means either no where-block or an AST built without source.
    # Excluded from equality and repr like `Node.span`: AST nodes
    # compare and print structurally, position-blind — an invariant
    # `fn_structural_hash` (vera/obligations/cache.py) and
    # `_remap_spans_inplace` (vera/transform.py) both lean on.
    where_span: Span | None = field(
        default=None, repr=False, compare=False,
    )


@dataclass(frozen=True)
class DataDecl(Decl):
    """Algebraic data type declaration."""
    name: str
    type_params: tuple[str, ...] | None
    invariant: Expr | None
    constructors: tuple[Constructor, ...]


@dataclass(frozen=True)
class Constructor(Node):
    """A data type constructor (nullary or with fields)."""
    name: str
    fields: tuple[TypeExpr, ...] | None  # None = nullary


@dataclass(frozen=True)
class TypeAliasDecl(Decl):
    """Type alias: type Name<T> = TypeExpr;"""
    name: str
    type_params: tuple[str, ...] | None
    type_expr: TypeExpr


@dataclass(frozen=True)
class EffectDecl(Decl):
    """Effect declaration with operations."""
    name: str
    type_params: tuple[str, ...] | None
    operations: tuple[OpDecl, ...]


@dataclass(frozen=True)
class OpDecl(Node):
    """Effect or ability operation declaration."""
    name: str
    param_types: tuple[TypeExpr, ...]
    return_type: TypeExpr


@dataclass(frozen=True)
class AbilityDecl(Decl):
    """Ability declaration with operations."""
    name: str
    type_params: tuple[str, ...] | None
    operations: tuple[OpDecl, ...]


@dataclass(frozen=True)
class AbilityConstraint(Node):
    """A constraint on a type variable: Eq<T>."""
    ability_name: str
    type_var: str


# =====================================================================
# Type Expressions
# =====================================================================

@dataclass(frozen=True)
class NamedType(TypeExpr):
    """Named type, possibly with type arguments: Int, Option<T>."""
    name: str
    type_args: tuple[TypeExpr, ...] | None


@dataclass(frozen=True)
class FnType(TypeExpr):
    """Function type: fn(Param -> Return) effects(...)."""
    params: tuple[TypeExpr, ...]
    return_type: TypeExpr
    effect: EffectRow


@dataclass(frozen=True)
class RefinementType(TypeExpr):
    """Refinement type: { @Type | predicate }."""
    base_type: TypeExpr
    predicate: Expr


# =====================================================================
# Expressions
# =====================================================================

# -- Binary / unary / index --

@dataclass(frozen=True)
class BinaryExpr(Expr):
    """Binary operator expression."""
    op: BinOp
    left: Expr
    right: Expr


@dataclass(frozen=True)
class UnaryExpr(Expr):
    """Unary operator expression (prefix)."""
    op: UnaryOp
    operand: Expr


@dataclass(frozen=True)
class IndexExpr(Expr):
    """Array index expression: collection[index]."""
    collection: Expr
    index: Expr


# -- Literals --

@dataclass(frozen=True)
class IntLit(Expr):
    """Integer literal."""
    value: int


@dataclass(frozen=True)
class FloatLit(Expr):
    """Float literal."""
    value: float


@dataclass(frozen=True)
class StringLit(Expr):
    """String literal."""
    value: str


@dataclass(frozen=True)
class InterpolatedString(Expr):
    """String with interpolated expressions: "text \\(expr) more".

    Parts alternate: str, Expr, str, Expr, ..., str.
    Always starts and ends with a string fragment (may be empty ``""``).
    """
    parts: tuple[str | Expr, ...]


@dataclass(frozen=True)
class BoolLit(Expr):
    """Boolean literal."""
    value: bool


@dataclass(frozen=True)
class UnitLit(Expr):
    """Unit literal: ()."""


@dataclass(frozen=True)
class HoleExpr(Expr):
    """Typed hole: ?  Placeholder expression for partial programs."""


# -- Slot references --

@dataclass(frozen=True)
class SlotRef(Expr):
    """Typed De Bruijn index: @Type.n or @Type<Args>.n."""
    type_name: str
    type_args: tuple[TypeExpr, ...] | None
    index: int


@dataclass(frozen=True)
class ResultRef(Expr):
    """Result reference: @Type.result."""
    type_name: str
    type_args: tuple[TypeExpr, ...] | None


# -- Calls --

@dataclass(frozen=True)
class FnCall(Expr):
    """Function call: name(args)."""
    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class ConstructorCall(Expr):
    """Constructor call with arguments: Some(42)."""
    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class NullaryConstructor(Expr):
    """Nullary constructor expression: None."""
    name: str
    #: The ADT this reference resolves to, when the COMPILER generated the
    #: node and already knows (#1414).  A parsed reference leaves it `None`
    #: and is resolved by name, as before.
    #:
    #: Code generation keys constructor ownership on a flat by-name table
    #: built across every ADT, so a user `data ZzBox { Less(Bool) }` takes
    #: the `Less` entry away from `Ordering` — and the desugaring of
    #: `compare(a, b)`, which emits bare `Less` / `Equal` / `Greater`, then
    #: rendered every `Ordering` in the program as the user's constructor.
    #: Those three references are the compiler's own and mean `Ordering`
    #: whatever the program declares, so they say so structurally rather
    #: than relying on a name lookup that a declaration can move.
    owner: str | None = None


@dataclass(frozen=True)
class QualifiedCall(Expr):
    """Qualified call: Module.function(args)."""
    qualifier: str
    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class ModuleCall(Expr):
    """Module-path call: path.to.module::function(args)."""
    path: tuple[str, ...]
    name: str
    args: tuple[Expr, ...]


# -- Lambda --

@dataclass(frozen=True)
class AnonFn(Expr):
    """Anonymous function / closure."""
    params: tuple[TypeExpr, ...]
    return_type: TypeExpr
    effect: EffectRow
    body: Block


# -- Control flow --

@dataclass(frozen=True)
class IfExpr(Expr):
    """If-then-else expression."""
    condition: Expr
    then_branch: Block
    else_branch: Block


@dataclass(frozen=True)
class MatchExpr(Expr):
    """Pattern match expression."""
    scrutinee: Expr
    arms: tuple[MatchArm, ...]


@dataclass(frozen=True)
class MatchArm(Node):
    """A single match arm: pattern -> expr."""
    pattern: Pattern
    body: Expr


@dataclass(frozen=True)
class Block(Expr):
    """Block expression: { stmt*; expr }."""
    statements: tuple[Stmt, ...]
    expr: Expr


# -- Effect handling --

@dataclass(frozen=True)
class HandleExpr(Expr):
    """Effect handler expression."""
    effect: EffectRefNode
    state: HandlerState | None
    clauses: tuple[HandlerClause, ...]
    body: Block


@dataclass(frozen=True)
class HandlerState(Node):
    """Handler initial state: (@Type = expr)."""
    type_expr: TypeExpr
    init_expr: Expr


@dataclass(frozen=True)
class HandlerClause(Node):
    """Handler operation clause: op_name(params) -> body [with @T = expr]."""
    op_name: str
    params: tuple[TypeExpr, ...]
    body: Expr
    state_update: tuple[TypeExpr, Expr] | None = None


@dataclass(frozen=True)
class _WithClause:
    """Internal sentinel for transformer: carries parsed with-clause data."""
    type_expr: TypeExpr
    init_expr: Expr


# -- Contract expressions --

@dataclass(frozen=True)
class OldExpr(Expr):
    """old(EffectRef) — state before effect execution."""
    effect_ref: EffectRefNode


@dataclass(frozen=True)
class NewExpr(Expr):
    """new(EffectRef) — state after effect execution."""
    effect_ref: EffectRefNode


@dataclass(frozen=True)
class AssertExpr(Expr):
    """assert(expr) — runtime assertion."""
    expr: Expr


@dataclass(frozen=True)
class AssumeExpr(Expr):
    """assume(expr) — verifier assumption."""
    expr: Expr


# -- Quantifiers --

@dataclass(frozen=True)
class ForallExpr(Expr):
    """Universal quantifier: forall(@Type, domain, predicate)."""
    binding_type: TypeExpr
    domain: Expr
    predicate: AnonFn


@dataclass(frozen=True)
class ExistsExpr(Expr):
    """Existential quantifier: exists(@Type, domain, predicate)."""
    binding_type: TypeExpr
    domain: Expr
    predicate: AnonFn


# -- Array --

@dataclass(frozen=True)
class ArrayLit(Expr):
    """Array literal: [a, b, c]."""
    elements: tuple[Expr, ...]


# =====================================================================
# Patterns
# =====================================================================

@dataclass(frozen=True)
class ConstructorPattern(Pattern):
    """Constructor pattern: Ctor(p1, p2)."""
    name: str
    sub_patterns: tuple[Pattern, ...]


@dataclass(frozen=True)
class NullaryPattern(Pattern):
    """Nullary constructor pattern: None."""
    name: str


@dataclass(frozen=True)
class BindingPattern(Pattern):
    """Binding pattern: @Type."""
    type_expr: TypeExpr


@dataclass(frozen=True)
class WildcardPattern(Pattern):
    """Wildcard pattern: _."""


@dataclass(frozen=True)
class IntPattern(Pattern):
    """Integer literal pattern."""
    value: int


@dataclass(frozen=True)
class StringPattern(Pattern):
    """String literal pattern."""
    value: str


@dataclass(frozen=True)
class BoolPattern(Pattern):
    """Boolean literal pattern."""
    value: bool


# =====================================================================
# Statements
# =====================================================================

@dataclass(frozen=True)
class LetStmt(Stmt):
    """Let binding: let @Type = expr;"""
    type_expr: TypeExpr
    value: Expr


@dataclass(frozen=True)
class LetDestruct(Stmt):
    """Tuple destructuring: let Ctor<@T, @U> = expr;"""
    constructor: str
    type_bindings: tuple[TypeExpr, ...]
    value: Expr


@dataclass(frozen=True)
class ExprStmt(Stmt):
    """Expression statement: expr;"""
    expr: Expr


# =====================================================================
# Contracts
# =====================================================================

@dataclass(frozen=True)
class Requires(Contract):
    """Precondition: requires(expr)."""
    expr: Expr


@dataclass(frozen=True)
class Ensures(Contract):
    """Postcondition: ensures(expr)."""
    expr: Expr


@dataclass(frozen=True)
class Decreases(Contract):
    """Termination measure: decreases(expr, ...)."""
    exprs: tuple[Expr, ...]


@dataclass(frozen=True)
class Invariant(Contract):
    """Type invariant: invariant(expr)."""
    expr: Expr


# =====================================================================
# Effects
# =====================================================================

@dataclass(frozen=True)
class PureEffect(EffectRow):
    """Pure effect: effects(pure)."""


@dataclass(frozen=True)
class EffectSet(EffectRow):
    """Effect set: effects(<E1, E2>)."""
    effects: tuple[EffectRefNode, ...]


@dataclass(frozen=True)
class EffectRef(EffectRefNode):
    """Effect reference: EffectName<TypeArgs>."""
    name: str
    type_args: tuple[TypeExpr, ...] | None


@dataclass(frozen=True)
class QualifiedEffectRef(EffectRefNode):
    """Qualified effect reference: Module.Effect<TypeArgs>."""
    module: str
    name: str
    type_args: tuple[TypeExpr, ...] | None


# =====================================================================
# Internal Sentinel Types (used by transformer, not exported)
# =====================================================================

@dataclass(frozen=True)
class _ForallVars:
    """Sentinel: forall type variable list."""
    vars: tuple[str, ...]
    constraints: tuple[AbilityConstraint, ...] | None = None


@dataclass(frozen=True)
class _WhereFns:
    """Sentinel: where-block function declarations."""
    fns: tuple[FnDecl, ...]
    # Span of the whole `where { ... }`, carried through to
    # `FnDecl.where_span` so the keyword line is addressable.
    span: Span | None = None


@dataclass(frozen=True)
class _TypeParams:
    """Sentinel: type parameter list."""
    params: tuple[str, ...]


@dataclass(frozen=True)
class _Signature:
    """Sentinel: function signature (params + return type)."""
    params: tuple[TypeExpr, ...]
    return_type: TypeExpr


@dataclass(frozen=True)
class _TupleDestruct:
    """Sentinel: tuple destructuring pattern."""
    constructor: str
    type_bindings: tuple[TypeExpr, ...]


# =====================================================================
# Source Text Formatting (for error messages)
# =====================================================================

def format_type_expr(te: TypeExpr) -> str:
    """Reconstruct Vera source text from a type expression AST node."""
    if isinstance(te, NamedType):
        if te.type_args:
            args = ", ".join(format_type_expr(a) for a in te.type_args)
            return f"@{te.name}<{args}>"
        return f"@{te.name}"
    if isinstance(te, RefinementType):
        return format_type_expr(te.base_type)
    return "@?"


def predicate_binder_ref(predicate: "Expr") -> "SlotRef | None":
    """A refinement predicate's binder REFERENCE — the first ``SlotRef`` the
    traversal below reaches, whole: head name and type arguments both.
    ``None`` if the predicate holds no ``SlotRef``.

    "First" is in TRAVERSAL order, which is neither source order nor
    outermost-first: the walk is a stack, so it descends the last field of a
    node before the first.  For the overwhelmingly common predicate — one
    closed over its single binder, every reference naming it — any of them is
    that binder and the order does not matter.  It is not universal, and the
    exception is a predicate containing a CLOSURE, which introduces a binder of
    its own: ``{ @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool) …
    { @Nat.0 >= 18 }) }`` yields the closure's ``@Nat.0``, so the key derived
    from it is ``Nat`` where the refinement's base is ``Array<Nat>``.  The
    consequence is conservative and pre-dates the key derivation: a value
    pushed under a key no reference resolves leaves the predicate
    untranslatable, which is a Tier-3 demotion, never a fact assumed about the
    wrong term.  ``tests/test_callee_contract_scope_1220_1225_1226.py``
    characterizes the shape.

    The reference rather than its name, because the binding-table key a
    reference resolves under is not its head — ``@Box<Cnt>.0`` looks itself up
    under ``Box<Nat>``, a rendering that needs the type arguments AND the
    naming environment.  :func:`~vera.naming.predicate_binder_key` is that
    derivation; this is the syntax it reads.  Both are shared, so the verifier,
    codegen, and SMT refined-return paths cannot drift apart (CR PR-review)."""
    stack: list[object] = [predicate]
    while stack:
        node = stack.pop()
        if isinstance(node, SlotRef):
            return node
        if isinstance(node, Node) and is_dataclass(node):
            for fld in fields(node):
                val = getattr(node, fld.name)
                if isinstance(val, Node):
                    stack.append(val)
                elif isinstance(val, (list, tuple)):
                    stack.extend(v for v in val if isinstance(v, Node))
    return None


def format_expr(expr: Expr) -> str:
    """Reconstruct Vera source text from an expression AST node.

    Produces human-readable representations for contract expressions
    in runtime error messages.
    """
    if isinstance(expr, IntLit):
        return str(expr.value)
    if isinstance(expr, FloatLit):
        return str(expr.value)
    if isinstance(expr, BoolLit):
        return "true" if expr.value else "false"
    if isinstance(expr, StringLit):
        return f'"{expr.value}"'
    if isinstance(expr, UnitLit):
        # #1248: without this arm the `<expr>` catch-all below swallowed every
        # Unit literal, so an obligation over `mk(())` described its call as
        # `mk(<expr>)` in `verify --json` and in E505 text — two calls that
        # differ only in a Unit argument became indistinguishable by
        # description.  A missing arm here never fails; it silently degrades.
        return "()"
    if isinstance(expr, InterpolatedString):
        parts = []
        for p in expr.parts:
            if isinstance(p, str):
                parts.append(p)
            else:
                parts.append(f"\\({format_expr(p)})")
        return '"' + "".join(parts) + '"'
    if isinstance(expr, ArrayLit):
        elements = ", ".join(format_expr(e) for e in expr.elements)
        return f"[{elements}]"
    if isinstance(expr, SlotRef):
        base = expr.type_name
        if expr.type_args:
            args = ", ".join(format_type_expr(a) for a in expr.type_args)
            base = f"{base}<{args}>"
        return f"@{base}.{expr.index}"
    if isinstance(expr, ResultRef):
        base = expr.type_name
        if expr.type_args:
            args = ", ".join(format_type_expr(a) for a in expr.type_args)
            base = f"{base}<{args}>"
        return f"@{base}.result"
    if isinstance(expr, BinaryExpr):
        left = format_expr(expr.left)
        right = format_expr(expr.right)
        return f"{left} {expr.op.value} {right}"
    if isinstance(expr, UnaryExpr):
        operand = format_expr(expr.operand)
        if expr.op == UnaryOp.NEG:
            return f"-{operand}"
        return f"!{operand}"
    if isinstance(expr, FnCall):
        args = ", ".join(format_expr(a) for a in expr.args)
        return f"{expr.name}({args})"
    if isinstance(expr, ModuleCall):
        path = ".".join(expr.path)
        args = ", ".join(format_expr(a) for a in expr.args)
        return f"{path}::{expr.name}({args})"
    if isinstance(expr, OldExpr):
        ref = expr.effect_ref
        if isinstance(ref, EffectRef):
            if ref.type_args:
                args = ", ".join(format_type_expr(a) for a in ref.type_args)
                return f"old({ref.name}<{args}>)"
            return f"old({ref.name})"
        return "old(...)"
    if isinstance(expr, NewExpr):
        ref = expr.effect_ref
        if isinstance(ref, EffectRef):
            if ref.type_args:
                args = ", ".join(format_type_expr(a) for a in ref.type_args)
                return f"new({ref.name}<{args}>)"
            return f"new({ref.name})"
        return "new(...)"
    if isinstance(expr, ForallExpr):
        binding = format_type_expr(expr.binding_type)
        domain = format_expr(expr.domain)
        return f"forall({binding}, {domain}, ...)"
    if isinstance(expr, ExistsExpr):
        binding = format_type_expr(expr.binding_type)
        domain = format_expr(expr.domain)
        return f"exists({binding}, {domain}, ...)"
    if isinstance(expr, IndexExpr):
        coll = format_expr(expr.collection)
        idx = format_expr(expr.index)
        return f"{coll}[{idx}]"
    return "<expr>"


def format_fn_signature(decl: FnDecl) -> str:
    """Format a function signature for error messages.

    Produces output like: clamp(@Int, @Int, @Int -> @Int)
    """
    params = ", ".join(format_type_expr(p) for p in decl.params)
    ret = format_type_expr(decl.return_type)
    return f"{decl.name}({params} -> {ret})"
