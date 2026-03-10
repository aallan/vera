"""Lark parse tree → Vera AST transformer.

Converts raw Lark Trees (from vera.parser.parse) into typed AST nodes
(from vera.ast). Uses Lark's Transformer class — methods are called
bottom-up, so children are already transformed when a parent runs.
"""

from __future__ import annotations

from typing import Any

from lark import Token, Transformer, Tree, v_args

from vera.ast import (
    AnonFn,
    ArrayLit,
    AssertExpr,
    AssumeExpr,
    BinaryExpr,
    BinOp,
    BindingPattern,
    Block,
    BoolLit,
    BoolPattern,
    Constructor,
    ConstructorCall,
    ConstructorPattern,
    Contract,
    DataDecl,
    Decl,
    Decreases,
    EffectDecl,
    EffectRef,
    EffectRefNode,
    EffectRow,
    EffectSet,
    Ensures,
    ExistsExpr,
    Expr,
    ExprStmt,
    FloatLit,
    FnCall,
    FnDecl,
    FnType,
    ForallExpr,
    HandleExpr,
    HandlerClause,
    HandlerState,
    IfExpr,
    ImportDecl,
    IndexExpr,
    InterpolatedString,
    IntLit,
    IntPattern,
    Invariant,
    LetDestruct,
    LetStmt,
    MatchArm,
    MatchExpr,
    ModuleCall,
    ModuleDecl,
    NamedType,
    NewExpr,
    NullaryConstructor,
    NullaryPattern,
    OldExpr,
    OpDecl,
    Program,
    PureEffect,
    QualifiedCall,
    QualifiedEffectRef,
    RefinementType,
    Requires,
    ResultRef,
    SlotRef,
    Span,
    StringLit,
    StringPattern,
    Stmt,
    TopLevelDecl,
    TypeAliasDecl,
    TypeExpr,
    UnaryExpr,
    UnaryOp,
    UnitLit,
    WildcardPattern,
    _ForallVars,
    _Signature,
    _TupleDestruct,
    _TypeParams,
    _WhereFns,
    _WithClause,
)
from vera.errors import Diagnostic, SourceLocation, TransformError


def _span_from_meta(meta: Any) -> Span | None:
    """Extract a Span from a Lark Tree's meta, if positions are available."""
    if hasattr(meta, "line") and meta.line is not None:
        return Span(
            line=meta.line,
            column=meta.column,
            end_line=meta.end_line,
            end_column=meta.end_column,
        )
    return None


def _transform_error(
    msg: str, meta: Any = None, *, error_code: str = "E010",
) -> TransformError:
    """Create a TransformError with optional location info."""
    loc = SourceLocation()
    if meta and hasattr(meta, "line") and meta.line is not None:
        loc = SourceLocation(line=meta.line, column=meta.column)
    return TransformError(Diagnostic(description=msg, location=loc,
                                      error_code=error_code))


# ---------------------------------------------------------------------------
# String escape sequence decoding (spec §1)
# ---------------------------------------------------------------------------

_SIMPLE_ESCAPES: dict[str, str] = {
    "\\": "\\",
    '"': '"',
    "n": "\n",
    "t": "\t",
    "r": "\r",
    "0": "\0",
}


def _decode_string_escapes(s: str, meta: Any = None) -> str:
    """Decode Vera escape sequences in a string literal body.

    Supports: ``\\\\``, ``\\"``, ``\\n``, ``\\t``, ``\\r``, ``\\0``,
    ``\\u{XXXX}`` (1-6 hex digits).  Any other escape raises E009.
    """
    if "\\" not in s:
        return s  # fast path — no escapes

    result: list[str] = []
    i = 0
    while i < len(s):
        if s[i] != "\\":
            result.append(s[i])
            i += 1
            continue

        # Backslash at end of string (shouldn't happen with valid grammar)
        if i + 1 >= len(s):
            raise _transform_error(
                "Invalid escape sequence: trailing backslash",
                meta, error_code="E009")

        nxt = s[i + 1]
        if nxt in _SIMPLE_ESCAPES:
            result.append(_SIMPLE_ESCAPES[nxt])
            i += 2
        elif nxt == "u":
            # \u{XXXX} — 1-6 hex digits
            if i + 2 >= len(s) or s[i + 2] != "{":
                raise _transform_error(
                    "Invalid unicode escape: expected '{' after \\u",
                    meta, error_code="E009")
            close = s.find("}", i + 3)
            if close == -1:
                raise _transform_error(
                    "Invalid unicode escape: missing '}'",
                    meta, error_code="E009")
            hex_str = s[i + 3:close]
            if not (1 <= len(hex_str) <= 6) or not all(
                c in "0123456789abcdefABCDEF" for c in hex_str
            ):
                raise _transform_error(
                    f"Invalid unicode escape: \\u{{{hex_str}}}",
                    meta, error_code="E009")
            code_point = int(hex_str, 16)
            if code_point > 0x10FFFF:
                raise _transform_error(
                    f"Unicode code point out of range: \\u{{{hex_str}}}",
                    meta, error_code="E009")
            result.append(chr(code_point))
            i = close + 1
        else:
            raise _transform_error(
                f"Invalid escape sequence: \\{nxt}",
                meta, error_code="E009")
    return "".join(result)


# ---------------------------------------------------------------------------
# String interpolation helpers (spec §4)
# ---------------------------------------------------------------------------

def _has_interpolation(raw: str) -> bool:
    """Check whether a raw (between-quotes) string contains ``\\(``."""
    i = 0
    while i < len(raw) - 1:
        if raw[i] == "\\" and raw[i + 1] == "(":
            return True
        if raw[i] == "\\":
            i += 2  # skip escaped char
        else:
            i += 1
    return False


def _split_interpolation(raw: str, meta: Any = None) -> list[str]:
    r"""Split a raw string on ``\(`` and matching ``)`` markers.

    Returns an alternating list ``[literal, expr, literal, expr, ..., literal]``
    where even-indexed elements are literal text and odd-indexed elements are
    expression source strings.
    """
    parts: list[str] = []
    buf: list[str] = []
    i = 0
    while i < len(raw):
        if raw[i] == "\\" and i + 1 < len(raw) and raw[i + 1] == "(":
            # Flush literal buffer
            parts.append("".join(buf))
            buf = []
            # Find matching ')' tracking paren depth
            depth = 1
            j = i + 2
            while j < len(raw) and depth > 0:
                if raw[j] == "(":
                    depth += 1
                elif raw[j] == ")":
                    depth -= 1
                j += 1
            if depth != 0:
                raise _transform_error(
                    "Unmatched '\\(' in string interpolation — "
                    "missing closing ')'.",
                    meta, error_code="E009",
                )
            expr_text = raw[i + 2:j - 1]
            if not expr_text.strip():
                raise _transform_error(
                    "Empty expression in string interpolation '\\()'.",
                    meta, error_code="E009",
                )
            parts.append(expr_text)
            i = j
        else:
            buf.append(raw[i])
            i += 1
    parts.append("".join(buf))
    return parts


def _parse_interp_expr(source: str, meta: Any = None) -> Expr:
    """Parse an interpolated expression by wrapping in a dummy function."""
    from vera.parser import parse as _parse

    wrapper = (
        "private fn interpExpr(@Unit -> @Unit)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {source} }}\n"
    )
    try:
        tree = _parse(wrapper)
    except Exception:
        raise _transform_error(
            f"Invalid expression in string interpolation: "
            f"\\({source})",
            meta, error_code="E009",
        )
    # Transform the parse tree and extract the body expression
    program = VeraTransformer().transform(tree)
    fn_decl = program.declarations[0].decl
    body = fn_decl.body
    if body.statements:
        raise _transform_error(
            "Statements are not allowed inside string interpolation. "
            "Only expressions may appear inside '\\(...)'.",
            meta, error_code="E009",
        )
    return body.expr


class VeraTransformer(Transformer):
    """Transforms a Lark parse tree into Vera AST nodes."""

    # =================================================================
    # Safety net — any unhandled grammar rule is a bug
    # =================================================================

    def __default__(self, data, children, meta):
        raise _transform_error(
            f"Unhandled grammar rule in AST transformer: '{data}'. "
            f"This is an internal compiler bug.",
            meta,
        )

    # =================================================================
    # Terminal handlers
    # =================================================================

    def LOWER_IDENT(self, token: Token) -> str:
        return str(token)

    def UPPER_IDENT(self, token: Token) -> str:
        return str(token)

    def INT_LIT(self, token: Token) -> int:
        return int(token)

    def FLOAT_LIT(self, token: Token) -> float:
        return float(token)

    def STRING_LIT(self, token: Token) -> str | list[str]:
        raw = str(token)[1:-1]  # Strip surrounding quotes
        if _has_interpolation(raw):
            return _split_interpolation(raw, token)
        return _decode_string_escapes(raw, token)

    # =================================================================
    # Program Structure
    # =================================================================

    @v_args(meta=True)
    def start(self, meta, children):
        module = None
        imports = []
        declarations = []
        for child in children:
            if isinstance(child, ModuleDecl):
                module = child
            elif isinstance(child, ImportDecl):
                imports.append(child)
            elif isinstance(child, TopLevelDecl):
                declarations.append(child)
        return Program(
            module=module,
            imports=tuple(imports),
            declarations=tuple(declarations),
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def module_decl(self, meta, children):
        # children: [tuple[str, ...]] (from module_path)
        return ModuleDecl(path=children[0], span=_span_from_meta(meta))

    def module_path(self, children):
        # children: [str, str, ...]
        return tuple(children)

    @v_args(meta=True)
    def import_decl(self, meta, children):
        # children: [tuple[str, ...], tuple[str, ...]?]
        path = children[0]
        names = children[1] if len(children) > 1 else None
        return ImportDecl(path=path, names=names, span=_span_from_meta(meta))

    def import_list(self, children):
        # children: [str, str, ...]
        return tuple(children)

    def import_name(self, children):
        return children[0]

    @v_args(meta=True)
    def fn_top_level(self, meta, children):
        # children: [str?, FnDecl]  — str is visibility
        if len(children) == 2:
            return TopLevelDecl(
                visibility=children[0], decl=children[1],
                span=_span_from_meta(meta),
            )
        return TopLevelDecl(
            visibility=None, decl=children[0],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def data_top_level(self, meta, children):
        # children: [str?, DataDecl]
        if len(children) == 2:
            return TopLevelDecl(
                visibility=children[0], decl=children[1],
                span=_span_from_meta(meta),
            )
        return TopLevelDecl(
            visibility=None, decl=children[0],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def top_level_decl(self, meta, children):
        # children: [TypeAliasDecl | EffectDecl]
        return TopLevelDecl(
            visibility=None, decl=children[0],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def visibility(self, meta, children):
        # String literals are discarded; recover from span length
        span = _span_from_meta(meta)
        if span:
            length = span.end_column - span.column
            return "public" if length == 6 else "private"
        return "public"  # fallback — should not happen  # pragma: no cover

    # =================================================================
    # Function Declarations
    # =================================================================

    @v_args(meta=True)
    def fn_decl(self, meta, children):
        # children: [_ForallVars?, str, _Signature, tuple[Contract],
        #            EffectRow, Block, _WhereFns?]
        idx = 0
        forall_vars = None
        if isinstance(children[idx], _ForallVars):
            forall_vars = children[idx].vars
            idx += 1
        name = children[idx]; idx += 1
        sig = children[idx]; idx += 1
        contracts = children[idx]; idx += 1
        effect = children[idx]; idx += 1
        body = children[idx]; idx += 1
        where_fns = None
        if idx < len(children) and isinstance(children[idx], _WhereFns):
            where_fns = children[idx].fns
        return FnDecl(
            name=name,
            forall_vars=forall_vars,
            params=sig.params,
            return_type=sig.return_type,
            contracts=contracts,
            effect=effect,
            body=body,
            where_fns=where_fns,
            span=_span_from_meta(meta),
        )

    def forall_clause(self, children):
        # children: [tuple[str, ...]] (from type_var_list)
        return _ForallVars(vars=children[0])

    def type_var_list(self, children):
        return tuple(children)

    @v_args(meta=True)
    def fn_signature(self, meta, children):
        # children: [tuple[TypeExpr, ...]?, TypeExpr]
        # If no params: [TypeExpr]
        # With params:  [tuple[TypeExpr, ...], TypeExpr]
        if len(children) == 1:
            return _Signature(params=(), return_type=children[0])
        return _Signature(params=children[0], return_type=children[1])

    def fn_params(self, children):
        # children: [TypeExpr, TypeExpr, ...]
        return tuple(children)

    def contract_block(self, children):
        return tuple(children)

    @v_args(meta=True)
    def requires_clause(self, meta, children):
        return Requires(expr=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def ensures_clause(self, meta, children):
        return Ensures(expr=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def decreases_clause(self, meta, children):
        return Decreases(exprs=tuple(children), span=_span_from_meta(meta))

    @v_args(meta=True)
    def effect_clause(self, meta, children):
        # children: [EffectRow]  (PureEffect or EffectSet via ?effect_row)
        return children[0]

    @v_args(meta=True)
    def pure_effect(self, meta, children):
        return PureEffect(span=_span_from_meta(meta))

    @v_args(meta=True)
    def effect_set(self, meta, children):
        # children: [tuple[EffectRefNode, ...]] (from effect_list)
        return EffectSet(effects=children[0], span=_span_from_meta(meta))

    def effect_list(self, children):
        return tuple(children)

    @v_args(meta=True)
    def effect_ref(self, meta, children):
        # children: [str, tuple[TypeExpr, ...]?]
        name = children[0]
        type_args = children[1] if len(children) > 1 else None
        return EffectRef(name=name, type_args=type_args,
                         span=_span_from_meta(meta))

    @v_args(meta=True)
    def qualified_effect_ref(self, meta, children):
        # children: [str, str, tuple[TypeExpr, ...]?]
        module = children[0]
        name = children[1]
        type_args = children[2] if len(children) > 2 else None
        return QualifiedEffectRef(
            module=module, name=name, type_args=type_args,
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def fn_body(self, meta, children):
        # children: [Block] (from block_contents)
        return children[0]

    def where_block(self, children):
        # children: [FnDecl, FnDecl, ...]
        return _WhereFns(fns=tuple(children))

    # =================================================================
    # Data Type Declarations
    # =================================================================

    @v_args(meta=True)
    def data_decl(self, meta, children):
        # children: [str, _TypeParams?, Expr?, tuple[Constructor, ...]]
        name = children[0]
        rest = children[1:]
        type_params = None
        invariant = None
        constructors = rest[-1]  # always last
        for item in rest[:-1]:
            if isinstance(item, _TypeParams):
                type_params = item.params
            elif isinstance(item, Expr):
                invariant = item
        return DataDecl(
            name=name,
            type_params=type_params,
            invariant=invariant,
            constructors=constructors,
            span=_span_from_meta(meta),
        )

    def type_params(self, children):
        # children: [tuple[str, ...]] (from type_var_list)
        return _TypeParams(params=children[0])

    @v_args(meta=True)
    def invariant_clause(self, meta, children):
        return children[0]  # just the expression

    def constructor_list(self, children):
        return tuple(children)

    @v_args(meta=True)
    def fields_constructor(self, meta, children):
        # children: [str, TypeExpr, TypeExpr, ...]
        return Constructor(
            name=children[0],
            fields=tuple(children[1:]),
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def nullary_constructor(self, meta, children):
        return Constructor(
            name=children[0], fields=None,
            span=_span_from_meta(meta),
        )

    # =================================================================
    # Type Aliases
    # =================================================================

    @v_args(meta=True)
    def type_alias_decl(self, meta, children):
        # children: [str, _TypeParams?, TypeExpr]
        name = children[0]
        if len(children) == 3 and isinstance(children[1], _TypeParams):
            type_params = children[1].params
            type_expr = children[2]
        else:
            type_params = None
            type_expr = children[-1]
        return TypeAliasDecl(
            name=name, type_params=type_params, type_expr=type_expr,
            span=_span_from_meta(meta),
        )

    # =================================================================
    # Effect Declarations
    # =================================================================

    @v_args(meta=True)
    def effect_decl(self, meta, children):
        # children: [str, _TypeParams?, OpDecl, OpDecl, ...]
        name = children[0]
        rest = children[1:]
        type_params = None
        ops_start = 0
        if rest and isinstance(rest[0], _TypeParams):
            type_params = rest[0].params
            ops_start = 1
        return EffectDecl(
            name=name,
            type_params=type_params,
            operations=tuple(rest[ops_start:]),
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def op_decl(self, meta, children):
        # children: [str, tuple[TypeExpr, ...]?, TypeExpr]
        name = children[0]
        if len(children) == 3:
            param_types = children[1]
            return_type = children[2]
        else:
            param_types = ()
            return_type = children[1]
        return OpDecl(
            name=name, param_types=param_types, return_type=return_type,
            span=_span_from_meta(meta),
        )

    def param_types(self, children):
        return tuple(children)

    # =================================================================
    # Type Expressions
    # =================================================================

    def type_expr(self, children):
        # Unwrap: fn_type and refinement_type get wrapped in type_expr
        return children[0]

    @v_args(meta=True)
    def named_type(self, meta, children):
        # children: [str, tuple[TypeExpr, ...]?]
        name = children[0]
        type_args = children[1] if len(children) > 1 else None
        return NamedType(
            name=name, type_args=type_args,
            span=_span_from_meta(meta),
        )

    def type_args(self, children):
        return tuple(children)

    @v_args(meta=True)
    def fn_type(self, meta, children):
        # children: [tuple[TypeExpr, ...]?, TypeExpr, EffectRow]
        if len(children) == 3:
            params = children[0]
            return_type = children[1]
            effect = children[2]
        else:
            params = ()
            return_type = children[0]
            effect = children[1]
        return FnType(
            params=params, return_type=return_type, effect=effect,
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def refinement_type(self, meta, children):
        # children: [TypeExpr, Expr]
        return RefinementType(
            base_type=children[0], predicate=children[1],
            span=_span_from_meta(meta),
        )

    # =================================================================
    # Expressions — Binary Operators
    # =================================================================

    @v_args(meta=True)
    def add_op(self, meta, children):
        return BinaryExpr(BinOp.ADD, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def sub_op(self, meta, children):
        return BinaryExpr(BinOp.SUB, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def mul_op(self, meta, children):
        return BinaryExpr(BinOp.MUL, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def div_op(self, meta, children):
        return BinaryExpr(BinOp.DIV, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def mod_op(self, meta, children):
        return BinaryExpr(BinOp.MOD, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def eq_op(self, meta, children):
        return BinaryExpr(BinOp.EQ, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def neq_op(self, meta, children):
        return BinaryExpr(BinOp.NEQ, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def lt_op(self, meta, children):
        return BinaryExpr(BinOp.LT, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def gt_op(self, meta, children):
        return BinaryExpr(BinOp.GT, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def le_op(self, meta, children):
        return BinaryExpr(BinOp.LE, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def ge_op(self, meta, children):
        return BinaryExpr(BinOp.GE, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def and_op(self, meta, children):
        return BinaryExpr(BinOp.AND, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def or_op(self, meta, children):
        return BinaryExpr(BinOp.OR, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def implies(self, meta, children):
        return BinaryExpr(BinOp.IMPLIES, children[0], children[1],
                          span=_span_from_meta(meta))

    @v_args(meta=True)
    def pipe(self, meta, children):
        return BinaryExpr(BinOp.PIPE, children[0], children[1],
                          span=_span_from_meta(meta))

    # =================================================================
    # Expressions — Unary Operators
    # =================================================================

    @v_args(meta=True)
    def not_op(self, meta, children):
        return UnaryExpr(UnaryOp.NOT, children[0],
                         span=_span_from_meta(meta))

    @v_args(meta=True)
    def neg_op(self, meta, children):
        return UnaryExpr(UnaryOp.NEG, children[0],
                         span=_span_from_meta(meta))

    # =================================================================
    # Expressions — Postfix
    # =================================================================

    @v_args(meta=True)
    def index_op(self, meta, children):
        return IndexExpr(children[0], children[1],
                         span=_span_from_meta(meta))

    # =================================================================
    # Expressions — Literals
    # =================================================================

    @v_args(meta=True)
    def int_lit(self, meta, children):
        return IntLit(value=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def float_lit(self, meta, children):
        return FloatLit(value=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def string_lit(self, meta, children):
        child = children[0]
        if isinstance(child, list):
            # Interpolated string — child is alternating [lit, expr, lit, ...]
            span = _span_from_meta(meta)
            resolved: list[str | Expr] = []
            for i, segment in enumerate(child):
                if i % 2 == 0:
                    # Literal fragment — decode escapes
                    resolved.append(
                        _decode_string_escapes(segment, meta)
                    )
                else:
                    # Expression — recursively parse
                    resolved.append(_parse_interp_expr(segment, meta))
            return InterpolatedString(
                parts=tuple(resolved), span=span,
            )
        return StringLit(value=child, span=_span_from_meta(meta))

    @v_args(meta=True)
    def true_lit(self, meta, children):
        return BoolLit(value=True, span=_span_from_meta(meta))

    @v_args(meta=True)
    def false_lit(self, meta, children):
        return BoolLit(value=False, span=_span_from_meta(meta))

    @v_args(meta=True)
    def unit_lit(self, meta, children):
        return UnitLit(span=_span_from_meta(meta))

    # =================================================================
    # Expressions — Slot and Result References
    # =================================================================

    @v_args(meta=True)
    def slot_ref(self, meta, children):
        # children: [str, int] or [str, tuple[TypeExpr, ...], int]
        if len(children) == 2:
            return SlotRef(
                type_name=children[0], type_args=None, index=children[1],
                span=_span_from_meta(meta),
            )
        return SlotRef(
            type_name=children[0], type_args=children[1],
            index=children[2], span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def result_ref(self, meta, children):
        # children: [str] or [str, tuple[TypeExpr, ...]]
        name = children[0]
        type_args = children[1] if len(children) > 1 else None
        return ResultRef(
            type_name=name, type_args=type_args,
            span=_span_from_meta(meta),
        )

    # =================================================================
    # Expressions — Function Calls and Constructors
    # =================================================================

    @v_args(meta=True)
    def func_call(self, meta, children):
        # children: [str, tuple[Expr, ...]?]
        name = children[0]
        args = children[1] if len(children) > 1 else ()
        return FnCall(name=name, args=args, span=_span_from_meta(meta))

    @v_args(meta=True)
    def constructor_call(self, meta, children):
        # children: [str, tuple[Expr, ...]?]
        name = children[0]
        args = children[1] if len(children) > 1 else ()
        return ConstructorCall(
            name=name, args=args, span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def nullary_constructor_expr(self, meta, children):
        return NullaryConstructor(
            name=children[0], span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def qualified_call(self, meta, children):
        # children: [str, str, tuple[Expr, ...]?]
        qualifier = children[0]
        name = children[1]
        args = children[2] if len(children) > 2 else ()
        return QualifiedCall(
            qualifier=qualifier, name=name, args=args,
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def module_call(self, meta, children):
        # children: [tuple[str, ...], str, tuple[Expr, ...]?]
        path = children[0]
        name = children[1]
        args = children[2] if len(children) > 2 else ()
        return ModuleCall(
            path=path, name=name, args=args,
            span=_span_from_meta(meta),
        )

    def arg_list(self, children):
        return tuple(children)

    # =================================================================
    # Expressions — Anonymous Functions
    # =================================================================

    @v_args(meta=True)
    def anonymous_fn(self, meta, children):
        # children: [tuple[TypeExpr, ...]?, TypeExpr, EffectRow, Block]
        # fn(fn_params? -> @type_expr) effect_clause fn_body
        idx = 0
        if isinstance(children[idx], tuple):
            params = children[idx]; idx += 1
        else:
            params = ()
        return_type = children[idx]; idx += 1
        effect = children[idx]; idx += 1
        body = children[idx]
        return AnonFn(
            params=params, return_type=return_type,
            effect=effect, body=body,
            span=_span_from_meta(meta),
        )

    # =================================================================
    # Expressions — Control Flow
    # =================================================================

    @v_args(meta=True)
    def if_expr(self, meta, children):
        # children: [Expr, Block, Block]
        return IfExpr(
            condition=children[0],
            then_branch=children[1],
            else_branch=children[2],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def match_expr(self, meta, children):
        # children: [Expr, MatchArm, MatchArm, ...]
        return MatchExpr(
            scrutinee=children[0],
            arms=tuple(children[1:]),
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def match_arm(self, meta, children):
        # children: [Pattern, Expr]
        return MatchArm(
            pattern=children[0], body=children[1],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def block_expr(self, meta, children):
        # children: [Block] (from block_contents)
        return children[0]

    @v_args(meta=True)
    def block_contents(self, meta, children):
        # children: [Stmt*, Expr]
        # Partition: everything except the last is a statement
        stmts = []
        for child in children[:-1]:
            if isinstance(child, Stmt):
                stmts.append(child)
        return Block(
            statements=tuple(stmts),
            expr=children[-1],
            span=_span_from_meta(meta),
        )

    # =================================================================
    # Expressions — Effect Handlers
    # =================================================================

    @v_args(meta=True)
    def handle_expr(self, meta, children):
        # children: [EffectRefNode, HandlerState?, HandlerClause+, Block]
        effect = children[0]
        rest = children[1:]
        state = None
        if isinstance(rest[0], HandlerState):
            state = rest[0]
            rest = rest[1:]
        # Last is body (Block), everything else is HandlerClause
        body = rest[-1]
        clauses = tuple(rest[:-1])
        return HandleExpr(
            effect=effect, state=state,
            clauses=clauses, body=body,
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def handler_state(self, meta, children):
        # children: [TypeExpr, Expr]
        return HandlerState(
            type_expr=children[0], init_expr=children[1],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def handler_clause(self, meta, children):
        # children: [str, tuple[TypeExpr, ...]?, Expr, _WithClause?]
        name = children[0]
        state_update = None
        if isinstance(children[-1], _WithClause):
            wc = children[-1]
            state_update = (wc.type_expr, wc.init_expr)
            children = children[:-1]
        if len(children) == 3:
            params = children[1]
            body = children[2]
        else:
            params = ()
            body = children[1]
        return HandlerClause(
            op_name=name, params=params, body=body,
            state_update=state_update, span=_span_from_meta(meta),
        )

    def with_clause(self, children):
        # children: [TypeExpr, Expr]
        return _WithClause(type_expr=children[0], init_expr=children[1])

    def handler_params(self, children):
        return tuple(children)

    # =================================================================
    # Expressions — Contract Expressions
    # =================================================================

    @v_args(meta=True)
    def old_expr(self, meta, children):
        return OldExpr(effect_ref=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def new_expr(self, meta, children):
        return NewExpr(effect_ref=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def assert_expr(self, meta, children):
        return AssertExpr(expr=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def assume_expr(self, meta, children):
        return AssumeExpr(expr=children[0], span=_span_from_meta(meta))

    # =================================================================
    # Expressions — Quantifiers
    # =================================================================

    @v_args(meta=True)
    def forall_expr(self, meta, children):
        # children: [TypeExpr, Expr, AnonFn]
        return ForallExpr(
            binding_type=children[0], domain=children[1],
            predicate=children[2], span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def exists_expr(self, meta, children):
        # children: [TypeExpr, Expr, AnonFn]
        return ExistsExpr(
            binding_type=children[0], domain=children[1],
            predicate=children[2], span=_span_from_meta(meta),
        )

    # =================================================================
    # Expressions — Array Literals
    # =================================================================

    @v_args(meta=True)
    def array_literal(self, meta, children):
        # children: [tuple[Expr, ...]?]
        elements = children[0] if children else ()
        return ArrayLit(elements=elements, span=_span_from_meta(meta))

    # =================================================================
    # Expressions — Parenthesised
    # =================================================================

    def paren_expr(self, children):
        return children[0]  # unwrap

    # =================================================================
    # Patterns
    # =================================================================

    @v_args(meta=True)
    def constructor_pattern(self, meta, children):
        # children: [str, Pattern, Pattern, ...]
        return ConstructorPattern(
            name=children[0], sub_patterns=tuple(children[1:]),
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def nullary_pattern(self, meta, children):
        return NullaryPattern(name=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def binding_pattern(self, meta, children):
        return BindingPattern(
            type_expr=children[0], span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def wildcard_pattern(self, meta, children):
        return WildcardPattern(span=_span_from_meta(meta))

    @v_args(meta=True)
    def int_pattern(self, meta, children):
        return IntPattern(value=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def string_pattern(self, meta, children):
        return StringPattern(value=children[0], span=_span_from_meta(meta))

    @v_args(meta=True)
    def true_pattern(self, meta, children):
        return BoolPattern(value=True, span=_span_from_meta(meta))

    @v_args(meta=True)
    def false_pattern(self, meta, children):
        return BoolPattern(value=False, span=_span_from_meta(meta))

    # =================================================================
    # Statements
    # =================================================================

    def statement(self, children):
        return children[0]

    @v_args(meta=True)
    def let_stmt(self, meta, children):
        # children: [TypeExpr, Expr]
        return LetStmt(
            type_expr=children[0], value=children[1],
            span=_span_from_meta(meta),
        )

    @v_args(meta=True)
    def let_destruct(self, meta, children):
        # children: [_TupleDestruct, Expr]
        td = children[0]
        return LetDestruct(
            constructor=td.constructor,
            type_bindings=td.type_bindings,
            value=children[1],
            span=_span_from_meta(meta),
        )

    def tuple_destruct(self, children):
        # children: [str, TypeExpr, TypeExpr, ...]
        return _TupleDestruct(
            constructor=children[0],
            type_bindings=tuple(children[1:]),
        )

    @v_args(meta=True)
    def expr_stmt(self, meta, children):
        return ExprStmt(expr=children[0], span=_span_from_meta(meta))


# =====================================================================
# Public API
# =====================================================================

_transformer = VeraTransformer()


def transform(tree: Tree[Any]) -> Program:
    """Transform a Lark parse tree into a Vera AST.

    Args:
        tree: A Lark Tree from vera.parser.parse().

    Returns:
        A Program AST node.

    Raises:
        TransformError: If an unhandled grammar rule is encountered.
    """
    return _transformer.transform(tree)
