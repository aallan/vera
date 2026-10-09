"""Lark parse tree → Vera AST transformer.

Converts raw Lark Trees (from vera.parser.parse) into typed AST nodes
(from vera.ast). Uses Lark's Transformer class — methods are called
bottom-up, so children are already transformed when a parent runs.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Any

from lark import Token, Transformer, Tree, v_args
from lark.exceptions import VisitError

from vera.lexical import ANNOTATIONS_ATTR, AnnotationLabel

from vera.ast import (
    AbilityConstraint,
    AbilityDecl,
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
    DataDecl,
    Decreases,
    EffectDecl,
    EffectRef,
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
    UnaryExpr,
    UnaryOp,
    UnitLit,
    HoleExpr,
    WildcardPattern,
    _ForallVars,
    _Signature,
    _TupleDestruct,
    _TypeParams,
    _WhereFns,
    _WithClause,
)
from vera.errors import (
    Diagnostic,
    ParseError,
    SourceLocation,
    TransformError,
    VeraError,
)


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
    rationale: str = "", fix: str = "", spec_ref: str = "",
) -> TransformError:
    """Create a TransformError with optional location info.

    E009 (user-reachable escape / interpolation errors) callers pass the
    full instruction fields; E010 (unhandled grammar rule) callers do not —
    a rule the grammar defines but the transformer misses is a compiler
    bug, not a user error, so there is no user-facing fix to offer (#966).
    """
    loc = SourceLocation()
    if meta and hasattr(meta, "line") and meta.line is not None:
        loc = SourceLocation(line=meta.line, column=meta.column)
    return TransformError(Diagnostic(  # diag-fields-exempt: fields threaded from call sites (E009 passes rationale/fix/spec_ref; E010 unhandled-rule sites report internal invariants, description-only — see the docstring)
        description=msg, location=loc, error_code=error_code,
        rationale=rationale, fix=fix, spec_ref=spec_ref))


#: The call forms a pipe can name: each has an argument list for the
#: piped value to join.
_PIPE_TARGETS = (FnCall, ConstructorCall, QualifiedCall, ModuleCall)

#: What a right operand that is not a call is, for E040's description.
_NOT_A_CALL: dict[type, str] = {
    IntLit: "an integer literal",
    FloatLit: "a float literal",
    StringLit: "a string literal",
    InterpolatedString: "a string literal",
    BoolLit: "a Boolean literal",
    UnitLit: "the unit value",
    HoleExpr: "a typed hole",
    SlotRef: "a slot reference",
    ResultRef: "a result reference",
    NullaryConstructor: "a constructor with no argument list",
    BinaryExpr: "an operator expression",
    UnaryExpr: "an operator expression",
    IndexExpr: "an index expression",
    ArrayLit: "an array literal",
    AnonFn: "an anonymous function",
    IfExpr: "an `if` expression",
    MatchExpr: "a `match` expression",
    Block: "a block",
    HandleExpr: "a `handle` expression",
}


def _pipe_operand_error(right: Expr, meta: Any) -> TransformError:
    """E040: the right operand of `|>` is not a call (spec §4.11.2)."""
    if isinstance(right, _PIPE_TARGETS):
        found = "a pipe"
    else:
        found = _NOT_A_CALL.get(type(right),
                                "an expression that is not a call")
    return _transform_error(
        f"The right operand of '|>' must be a call; this one is {found}.",
        right.span if right.span is not None else meta,
        error_code="E040",
        rationale=(
            "'a |> f(b)' is the call 'f(a, b)': the pipe passes its left "
            "operand as the first argument of the call on its right.  Only "
            "a call written with its argument list — a function, a "
            "built-in, a constructor, an effect operation or a "
            "module-qualified function — has an argument list for the "
            "piped value to join."),
        fix=(
            "Write the right operand as a call, as in '@Int.0 |> abs()', or "
            "apply the function directly: 'abs(@Int.0)'.  Every other "
            "operator binds tighter than '|>', so 'a |> f() + 1' pipes "
            "into 'f() + 1'; write '(a |> f()) + 1' to add to the call's "
            "result.  To chain calls, write the stages in order: "
            "'a |> f() |> g()' is 'g(f(a))'."),
        spec_ref='Chapter 4, Section 4.11.2 "Pipe Operator"',
    )


_E009_ESCAPE_RATIONALE = (
    "Vera strings accept a closed set of escape sequences so string "
    "literals are unambiguous; an unrecognised escape is more likely a "
    "typo than an intention, and silently passing it through would change "
    "the string's meaning."
)
_E009_ESCAPE_FIX = (
    'Use one of the valid escapes — \\\\, \\", \\n, \\t, \\r, \\0, '
    "\\u{XXXX} (1-6 hex digits), or \\( for interpolation — or escape the "
    "backslash itself (\\\\) if a literal backslash is intended."
)
_E009_ESCAPE_SPEC = 'Chapter 1, Section 1.6 "Literals"'
_E009_INTERP_RATIONALE = (
    "String interpolation embeds a full Vera expression inside \\(...); a "
    "malformed or empty segment cannot be parsed as one, so the string "
    "has no well-defined value."
)
_E009_INTERP_FIX = (
    "Close every \\( with a matching ) and put exactly one expression "
    "(not a statement) inside it."
)
_E009_INTERP_SPEC = 'Chapter 4, Section 4.13.1 "String Interpolation"'


def _escape_error(msg: str, meta: Any = None) -> TransformError:
    """An E009 for the invalid-escape class, with full instruction fields."""
    return _transform_error(
        msg, meta, error_code="E009",
        rationale=_E009_ESCAPE_RATIONALE, fix=_E009_ESCAPE_FIX,
        spec_ref=_E009_ESCAPE_SPEC)


def _interp_error(msg: str, meta: Any = None) -> TransformError:
    """An E009 for the malformed-interpolation class, with full fields."""
    return _transform_error(
        msg, meta, error_code="E009",
        rationale=_E009_INTERP_RATIONALE, fix=_E009_INTERP_FIX,
        spec_ref=_E009_INTERP_SPEC)


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
            raise _escape_error(
                "Invalid escape sequence: trailing backslash", meta)

        nxt = s[i + 1]
        if nxt in _SIMPLE_ESCAPES:
            result.append(_SIMPLE_ESCAPES[nxt])
            i += 2
        elif nxt == "u":
            # \u{XXXX} — 1-6 hex digits
            if i + 2 >= len(s) or s[i + 2] != "{":
                raise _escape_error(
                    "Invalid unicode escape: expected '{' after \\u", meta)
            close = s.find("}", i + 3)
            if close == -1:
                raise _escape_error(
                    "Invalid unicode escape: missing '}'", meta)
            hex_str = s[i + 3:close]
            if not (1 <= len(hex_str) <= 6) or not all(
                c in "0123456789abcdefABCDEF" for c in hex_str
            ):
                raise _escape_error(
                    f"Invalid unicode escape: \\u{{{hex_str}}}", meta)
            code_point = int(hex_str, 16)
            if code_point > 0x10FFFF:
                raise _escape_error(
                    f"Unicode code point out of range: \\u{{{hex_str}}}", meta)
            result.append(chr(code_point))
            i = close + 1
        else:
            raise _escape_error(
                f"Invalid escape sequence: \\{nxt}", meta)
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


def _split_interpolation(
    raw: str, meta: Any = None,
) -> list[str | tuple[str, int]]:
    r"""Split a raw string on ``\(`` and matching ``)`` markers.

    Returns an alternating list ``[literal, expr, literal, expr, ..., literal]``
    where even-indexed elements are literal text (``str``) and odd-indexed
    elements are expression segments as ``(expr_text, offset_in_raw)``
    tuples.  The offset is the index of the ``\`` of the ``\(`` opener
    within ``raw`` — used by ``string_lit`` to compute original-source
    coordinates for span remapping (issue #634).
    """
    parts: list[str | tuple[str, int]] = []
    buf: list[str] = []
    i = 0
    while i < len(raw):
        if raw[i] == "\\" and i + 1 < len(raw):
            # An escape sequence — either ``\(`` which opens an
            # interpolation, or one of the literal escapes (``\\``,
            # ``\n``, ``\t``, ``\"``, ``\u{...}``) that the
            # downstream ``_decode_string_escapes`` will resolve on
            # the literal fragments.  Mirror the escape-skipping
            # logic from ``_has_interpolation`` so a literal
            # ``\\(`` (backslash + literal paren, NOT an
            # interpolation opener) is treated as two literal
            # characters rather than mis-segmented as the second
            # ``\(`` opening a new interpolation.  Pre-fix, the two
            # helpers disagreed: ``_has_interpolation`` saw a string
            # like ``"\\("`` as having no interpolation, but
            # ``_split_interpolation`` mis-parsed it.  CodeRabbit
            # caught the divergence on PR #649.
            if raw[i + 1] == "(":
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
                    raise _interp_error(
                        "Unmatched '\\(' in string interpolation — "
                        "missing closing ')'.", meta)
                expr_text = raw[i + 2:j - 1]
                if not expr_text.strip():
                    raise _interp_error(
                        "Empty expression in string interpolation '\\()'.",
                        meta)
                parts.append((expr_text, i))
                i = j
            else:
                # Any other escape: pass both chars through as
                # literal text and advance by 2 so we don't re-scan
                # the escaped character (the downstream
                # ``_decode_string_escapes`` on the literal fragment
                # is what actually performs the decode).
                buf.append(raw[i])
                buf.append(raw[i + 1])
                i += 2
        else:
            buf.append(raw[i])
            i += 1
    parts.append("".join(buf))
    return parts


# Wrapper layout used by `_parse_interp_expr` to make the segment
# parseable as a function body.  The segment is placed at line 3,
# column 3 (after `{ `) of the synthetic wrapper.  These constants
# are the offsets we subtract from parsed-span coordinates when
# remapping back to original-source positions for issue #634.
_INTERP_WRAPPER_LINE = 3
_INTERP_WRAPPER_COL = 3


def _remap_spans_inplace(
    node: Any, mapper: Any, _seen: set[int] | None = None,
) -> None:
    """Walk ``node`` and all descendants, replacing every ``Span`` field
    in-place via ``mapper(span) -> Span``: ``span``, and a piped call's
    ``stage_span`` beside it.

    Uses ``object.__setattr__`` to bypass the frozen-dataclass guard;
    ``ast.Node.span`` is declared with ``compare=False`` precisely so
    late updates like this can correct synthetic-wrapper coordinates
    without breaking equality semantics, and so is every other position.
    Walks ``list`` / ``tuple`` children and recurses into nested dataclass
    nodes.

    Used by ``_parse_interp_expr`` to remap spans from interpolation
    synthetic-wrapper coordinates back to original-source positions.
    Closes #634.
    """
    from dataclasses import fields as _dc_fields

    if _seen is None:
        _seen = set()
    if node is None:
        return
    if isinstance(node, (list, tuple)):
        for item in node:
            _remap_spans_inplace(item, mapper, _seen)
        return
    if not hasattr(node, "__dataclass_fields__"):
        return
    nid = id(node)
    if nid in _seen:
        return
    _seen.add(nid)
    for f in _dc_fields(node):
        val = getattr(node, f.name)
        if isinstance(val, Span):
            object.__setattr__(node, f.name, mapper(val))
        elif isinstance(val, (list, tuple)):
            for item in val:
                _remap_spans_inplace(item, mapper, _seen)
        elif hasattr(val, "__dataclass_fields__"):
            _remap_spans_inplace(val, mapper, _seen)


def _interp_source_point(line: int, col: int, base_line: int,
                         base_col: int) -> tuple[int, int]:
    """A position in the interpolation wrapper, in the original source.

    The wrapper places the segment at line 3, col 3 (after `{ `), so a
    position at (line=3, col=N) inside the wrapper is (base_line,
    base_col + (N - 3)) in the source.  Multi-line segments (rare —
    interpolation expressions are almost always single-line) get a per-line
    offset fallback."""
    if line == _INTERP_WRAPPER_LINE:
        return base_line, base_col + (col - _INTERP_WRAPPER_COL)
    return base_line + (line - _INTERP_WRAPPER_LINE), col


def _parse_interp_expr(
    source: str,
    meta: Any = None,
    base_line: int | None = None,
    base_col: int | None = None,
) -> Expr:
    """Parse an interpolated expression by wrapping in a dummy function.

    When ``base_line`` and ``base_col`` are provided, the parsed
    expression's spans are remapped from synthetic-wrapper coordinates
    back to original-source positions, so diagnostics on AST nodes
    constructed here (notably ``SlotRef`` nodes inside
    ``InterpolatedString.parts``) point at the right source line and
    column instead of landing on wrapper line 3.  Closes #634.
    """
    from vera.parser import parse as _parse

    wrapper = (
        "private fn interpExpr(@Unit -> @Unit)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {source} }}\n"
    )
    try:
        tree = _parse(wrapper)
    except ParseError:
        # Only a *syntax* failure means the user's interpolation is at
        # fault.  `parse` funnels every such failure — the grammar's own
        # `LarkError` and the malformed-comment diagnostics — through
        # `ParseError`, so anything else reaching here is a compiler bug
        # and must surface as itself rather than be reported back to the
        # user as an invalid interpolation.
        raise _interp_error(
            f"Invalid expression in string interpolation: "
            f"\\({source})", meta)
    # Transform the parse tree and extract the body expression
    try:
        program = VeraTransformer().transform(tree)
    except VisitError as exc:
        # A user error the transform reports inside the segment (E040, a
        # pipe whose right operand is not a call) is located in wrapper
        # coordinates: move it to the segment's place in the source.
        inner = _unwrap_visit_error(exc)
        if (isinstance(inner, TransformError) and base_line is not None
                and base_col is not None
                and inner.diagnostic.location.line):
            loc = inner.diagnostic.location
            loc.line, loc.column = _interp_source_point(
                loc.line, loc.column, base_line, base_col)
        if inner is not None:
            raise inner from None
        raise
    fn_decl = program.declarations[0].decl
    body = fn_decl.body
    if body.statements:
        raise _interp_error(
            "Statements are not allowed inside string interpolation. "
            "Only expressions may appear inside '\\(...)'.", meta)
    expr = body.expr
    if base_line is not None and base_col is not None:
        line0, col0 = base_line, base_col

        def _remap(s: Span) -> Span:
            new_line, new_col = _interp_source_point(
                s.line, s.column, line0, col0)
            new_end_line, new_end_col = _interp_source_point(
                s.end_line, s.end_column, line0, col0)
            return Span(
                line=new_line, column=new_col,
                end_line=new_end_line, end_column=new_end_col,
            )

        _remap_spans_inplace(expr, _remap)
    return expr


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

    def STRING_LIT(
        self, token: Token,
    ) -> str | list[str | tuple[str, int]]:
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
        forall_constraints = None
        if isinstance(children[idx], _ForallVars):
            forall_vars = children[idx].vars
            forall_constraints = children[idx].constraints
            idx += 1
        name = children[idx]
        idx += 1
        sig = children[idx]
        idx += 1
        contracts = children[idx]
        idx += 1
        effect = children[idx]
        idx += 1
        body = children[idx]
        idx += 1
        where_fns = None
        where_span = None
        if idx < len(children) and isinstance(children[idx], _WhereFns):
            where_fns = children[idx].fns
            where_span = children[idx].span
        return FnDecl(
            name=name,
            forall_vars=forall_vars,
            forall_constraints=forall_constraints,
            params=sig.params,
            return_type=sig.return_type,
            contracts=contracts,
            effect=effect,
            body=body,
            where_fns=where_fns,
            where_span=where_span,
            span=_span_from_meta(meta),
        )

    def forall_clause(self, children):
        # Alt 1: [tuple[str, ...]]
        # Alt 2: [tuple[str, ...], tuple[AbilityConstraint, ...]]
        if len(children) == 1:
            return _ForallVars(vars=children[0])
        return _ForallVars(vars=children[0], constraints=children[1])

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

    @v_args(meta=True)
    def where_block(self, meta, children):
        # children: [FnDecl, FnDecl, ...]
        # The span starts at the `where` keyword, which is filtered out
        # of the tree; only the rule's own meta records where it began,
        # and the formatter needs that line to anchor a comment written
        # above the block.
        return _WhereFns(fns=tuple(children), span=_span_from_meta(meta))

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
    # Ability Declarations
    # =================================================================

    @v_args(meta=True)
    def ability_decl(self, meta, children):
        # children: [str, _TypeParams?, OpDecl, OpDecl, ...]
        name = children[0]
        rest = children[1:]
        type_params = None
        ops_start = 0
        if rest and isinstance(rest[0], _TypeParams):
            type_params = rest[0].params
            ops_start = 1
        return AbilityDecl(
            name=name,
            type_params=type_params,
            operations=tuple(rest[ops_start:]),
            span=_span_from_meta(meta),
        )

    def ability_constraint_list(self, children):
        return tuple(children)

    @v_args(meta=True)
    def ability_constraint(self, meta, children):
        # children: [str (ability name), str (type var)]
        return AbilityConstraint(
            ability_name=children[0], type_var=children[1],
            span=_span_from_meta(meta),
        )

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
        # `a |> f(b, c)` is the call `f(a, b, c)` (spec §4.11.2), built here
        # once so that no later phase sees a pipe.  The call keeps its own
        # node type, so a module call keeps the path that routes it, and
        # takes the pipe's span, which owns the call; `piped` tells the
        # formatter to print the pipe back, and `stage_span` keeps where
        # `f(b, c)` is written, where a diagnostic about the call itself is
        # placed (`ast._stage`).
        left, right = children
        if not isinstance(right, _PIPE_TARGETS) or right.piped:
            raise _pipe_operand_error(right, meta)
        return replace(right, args=(left, *right.args),
                       span=_span_from_meta(meta), piped=True,
                       stage_span=right.span)

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
            # Interpolated string — child is alternating
            # [lit_str, (expr_text, offset), lit_str, ...].
            span = _span_from_meta(meta)
            resolved: list[str | Expr] = []
            # Compute original-source coordinates for span remapping
            # (#634).  The opening `"` of the string literal is at
            # `meta.column`; raw content starts at `meta.column + 1`.
            # An expression segment whose `\(` opener is at offset
            # `off` within raw has its expression text starting at
            # original column `meta.column + 1 + off + 2`
            # (= `meta.column + off + 3`).  We assume the string
            # literal is on a single line — multi-line interpolation
            # expressions are an edge case that still gets correct
            # line numbers via the per-line offset fallback in
            # `_remap_spans_inplace`'s mapper.
            meta_line = getattr(meta, "line", None)
            meta_col = getattr(meta, "column", None)
            # The alternating layout — even indices = str (literal
            # fragment), odd indices = (expr_text, raw_offset) tuple —
            # is guaranteed by `_split_interpolation`'s contract.
            # Dispatching on isinstance gives both runtime safety and
            # mypy narrowing without `assert` (which `ruff S101`
            # forbids in production code, since `python -O` strips
            # asserts).
            for segment in child:
                if isinstance(segment, str):
                    # Literal fragment — decode escapes
                    resolved.append(
                        _decode_string_escapes(segment, meta)
                    )
                else:
                    # Expression — recursively parse, with span remap.
                    expr_text, off = segment
                    if meta_line is not None and meta_col is not None:
                        base_line = meta_line
                        base_col = meta_col + off + 3
                    else:
                        base_line = None
                        base_col = None
                    resolved.append(_parse_interp_expr(
                        expr_text, meta,
                        base_line=base_line, base_col=base_col,
                    ))
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

    @v_args(meta=True)
    def hole_expr(self, meta, children):
        return HoleExpr(span=_span_from_meta(meta))

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
            params = children[idx]
            idx += 1
        else:
            params = ()
        return_type = children[idx]
        idx += 1
        effect = children[idx]
        idx += 1
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


def _unwrap_visit_error(exc: VisitError) -> VeraError | None:
    """Walk a (possibly nested) ``VisitError`` chain to the ``VeraError`` it
    wraps, or ``None`` if the chain bottoms out in something else.

    lark wraps exceptions raised in token/rule callbacks in ``VisitError``
    once per transformer boundary crossed — a nested transformer (e.g.
    ``_parse_interp_expr``'s inner ``VeraTransformer`` running inside the
    outer transformer's ``STRING_LIT`` callback) can therefore produce a
    doubly-wrapped chain.  Not user-reachable today (interpolation segments
    cannot contain nested string literals, and the inner transformer's other
    token callbacks cannot raise on grammar-valid input), but flattening the
    whole chain makes the #966 boundary robust to future nesting
    (PR #968 review)."""
    inner: BaseException = exc.orig_exc
    while isinstance(inner, VisitError):
        inner = inner.orig_exc
    return inner if isinstance(inner, VeraError) else None


_FAR_FUTURE = (1 << 30, 0)


def _label_between(
    labels: tuple[AnnotationLabel, ...],
    lower: tuple[int, int],
    upper: tuple[int, int],
) -> str | None:
    """The label in ``[lower, upper)``, or None.

    Only whitespace and punctuation separate a binding from its label, so
    the first match is the right one; anything past ``upper`` belongs to
    the next binding.
    """
    for label in labels:
        # depth 0 is outside the signature's parens, so however close it
        # sits to a slot it is an ordinary comment, not a label (spec 1.3).
        if label.depth > 0 and lower <= label.start < upper:
            return label.text
    return None


def _annotate_fn(fn: FnDecl, labels: tuple[AnnotationLabel, ...]) -> FnDecl:
    """Attach annotation-comment labels to one function's binding slots.

    A label follows the slot it names, so each slot claims the first
    label between its own end and the start of the next slot.  The return
    slot has no following slot, so it is bounded by the first contract
    (or the body) — otherwise a comment sitting anywhere later in the
    declaration would be read as the return's label.
    """
    sites: list[Any] = [*fn.params, fn.return_type]

    if fn.contracts and fn.contracts[0].span is not None:
        tail = (fn.contracts[0].span.line, fn.contracts[0].span.column)
    elif fn.body.span is not None:
        tail = (fn.body.span.line, fn.body.span.column)
    else:
        tail = _FAR_FUTURE

    found: list[str | None] = []
    for i, site in enumerate(sites):
        if site.span is None:
            found.append(None)
            continue
        nxt = sites[i + 1] if i + 1 < len(sites) else None
        upper = (
            (nxt.span.line, nxt.span.column)
            if nxt is not None and nxt.span is not None
            else tail
        )
        lower = (site.span.end_line, site.span.end_column)
        found.append(_label_between(labels, lower, upper))

    return replace(
        fn,
        param_annotations=tuple(found[:-1]),
        return_annotation=found[-1],
        where_fns=(
            tuple(_annotate_fn(w, labels) for w in fn.where_fns)
            if fn.where_fns is not None
            else None
        ),
    )


def _attach_annotations(
    program: Program,
    labels: tuple[AnnotationLabel, ...],
) -> Program:
    """Populate every function's annotation labels from the source scan.

    Runs even when ``labels`` is empty, so an unlabelled function reports
    a tuple of Nones rather than "unknown" — the two are different facts,
    and only the latter should be indistinguishable from an AST built
    without source.
    """
    return replace(program, declarations=tuple(
        replace(tld, decl=_annotate_fn(tld.decl, labels))
        if isinstance(tld.decl, FnDecl) else tld
        for tld in program.declarations
    ))


def transform(tree: Tree[Any]) -> Program:
    """Transform a Lark parse tree into a Vera AST.

    Args:
        tree: A Lark Tree from vera.parser.parse().

    Returns:
        A Program AST node.

    Raises:
        TransformError: If an unhandled grammar rule is encountered, or a
            user-facing E009 (invalid escape / malformed interpolation) is
            raised inside a token callback — lark wraps exceptions from
            token callbacks in ``VisitError``, which would otherwise escape
            the CLI's ``except VeraError`` as a raw traceback (#966).
    """
    try:
        program = _transformer.transform(tree)
    except VisitError as exc:
        inner = _unwrap_visit_error(exc)
        if inner is not None:
            raise inner from None
        raise

    # Annotation comments are `%ignore`d by the grammar, so `parse()`
    # carries them on the tree for spec 1.3's "preserved in the AST".
    # A tree built by hand has no such attribute and keeps None labels,
    # which is why the check is for presence rather than truthiness — an
    # empty scan still means "this source has no labels", not "unknown".
    labels = getattr(tree, ANNOTATIONS_ATTR, None)
    if labels is not None:
        program = _attach_annotations(program, labels)
    return program
