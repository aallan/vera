"""Vera AST node definitions.

Frozen dataclasses representing the typed abstract syntax tree.
Every node carries an optional source span for error reporting.
The hierarchy is shallow: Node → category base → concrete node.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields
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


@dataclass(frozen=True)
class Node:
    """Abstract base for all AST nodes."""
    span: Span | None = field(default=None, kw_only=True, repr=False, compare=False)

    def to_dict(self) -> dict[str, Any]:
        """Serialise to a JSON-compatible dict."""
        result: dict[str, Any] = {"_type": type(self).__name__}
        for f in fields(self):
            if f.name == "span":
                val = getattr(self, f.name)
                result["span"] = (
                    {"line": val.line, "column": val.column,
                     "end_line": val.end_line, "end_column": val.end_column}
                    if val else None
                )
                continue
            val = getattr(self, f.name)
            result[f.name] = _serialise(val)
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
    params: tuple[TypeExpr, ...]
    return_type: TypeExpr
    contracts: tuple[Contract, ...]
    effect: EffectRow
    body: Block
    where_fns: tuple[FnDecl, ...] | None


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
    """Effect operation declaration."""
    name: str
    param_types: tuple[TypeExpr, ...]
    return_type: TypeExpr


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
class BoolLit(Expr):
    """Boolean literal."""
    value: bool


@dataclass(frozen=True)
class UnitLit(Expr):
    """Unit literal: ()."""


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


@dataclass(frozen=True)
class QualifiedCall(Expr):
    """Qualified call: Module.function(args)."""
    qualifier: str
    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class ModuleCall(Expr):
    """Module-path call: path.to.module.function(args)."""
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


@dataclass(frozen=True)
class _WhereFns:
    """Sentinel: where-block function declarations."""
    fns: tuple[FnDecl, ...]


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
