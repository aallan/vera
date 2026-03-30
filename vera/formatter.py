"""Vera canonical code formatter.

Formats Vera source code to the canonical form defined in
Spec Section 1.8.  Preserves comments by extracting them
before parsing and re-attaching them to the formatted output.

Public API
----------
format_source(source, file=None) -> str
    Parse *source*, format the AST, re-insert comments,
    and return the canonically-formatted string.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

_STRING_ENCODE_MAP = {
    "\\": "\\\\",
    '"': '\\"',
    "\n": "\\n",
    "\t": "\\t",
    "\r": "\\r",
    "\0": "\\0",
}


def _encode_string_escapes(s: str) -> str:
    """Re-encode special characters as Vera escape sequences."""
    return "".join(_STRING_ENCODE_MAP.get(c, c) for c in s)


from vera.ast import (
    AbilityDecl,
    AnonFn,
    ArrayLit,
    AssertExpr,
    AssumeExpr,
    BinaryExpr,
    BinOp,
    Block,
    BoolLit,
    BoolPattern,
    BindingPattern,
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
    NullaryConstructor,
    NullaryPattern,
    OldExpr,
    NewExpr,
    OpDecl,
    Pattern,
    Program,
    PureEffect,
    QualifiedCall,
    QualifiedEffectRef,
    RefinementType,
    Requires,
    ResultRef,
    SlotRef,
    Stmt,
    StringLit,
    StringPattern,
    TopLevelDecl,
    TypeAliasDecl,
    TypeExpr,
    UnaryExpr,
    UnaryOp,
    UnitLit,
    HoleExpr,
    WildcardPattern,
)
from vera.parser import parse as vera_parse, parse_file
from vera.transform import transform


# =====================================================================
# Comment extraction
# =====================================================================

@dataclass
class Comment:
    """A comment extracted from source text."""
    kind: str       # "line" | "block" | "annotation"
    text: str       # Full text including delimiters
    line: int       # 1-based start line
    end_line: int   # 1-based end line
    inline: bool    # True if code precedes this comment on the same line


def extract_comments(source: str) -> list[Comment]:
    """Extract all comments from Vera source, preserving positions."""
    comments: list[Comment] = []
    lines = source.split("\n")
    i = 0
    src = source
    pos = 0

    while pos < len(src):
        # Line comment: --
        if src[pos:pos + 2] == "--":
            line_no = source[:pos].count("\n") + 1
            end = src.find("\n", pos)
            if end == -1:
                end = len(src)
            text = src[pos:end]
            col = pos - source.rfind("\n", 0, pos) - 1
            # Check if code precedes this comment on the same line
            line_start = source.rfind("\n", 0, pos) + 1
            before = source[line_start:pos]
            inline = before.strip() != ""
            comments.append(Comment(
                kind="line", text=text, line=line_no,
                end_line=line_no, inline=inline,
            ))
            pos = end
            continue

        # Block comment: {- ... -}  (nestable)
        if src[pos:pos + 2] == "{-":
            start_line = source[:pos].count("\n") + 1
            line_start = source.rfind("\n", 0, pos) + 1
            before = source[line_start:pos]
            inline = before.strip() != ""
            depth = 1
            j = pos + 2
            while j < len(src) and depth > 0:
                if src[j:j + 2] == "{-":
                    depth += 1
                    j += 2
                elif src[j:j + 2] == "-}":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            text = src[pos:j]
            end_line = source[:j].count("\n") + 1
            comments.append(Comment(
                kind="block", text=text, line=start_line,
                end_line=end_line, inline=inline,
            ))
            pos = j
            continue

        # Annotation comment: /* ... */
        if src[pos:pos + 2] == "/*":
            start_line = source[:pos].count("\n") + 1
            line_start = source.rfind("\n", 0, pos) + 1
            before = source[line_start:pos]
            inline = before.strip() != ""
            end = src.find("*/", pos + 2)
            if end == -1:
                end = len(src)
            else:
                end += 2
            text = src[pos:end]
            end_line = source[:end].count("\n") + 1
            comments.append(Comment(
                kind="annotation", text=text, line=start_line,
                end_line=end_line, inline=inline,
            ))
            pos = end
            continue

        # Inside a string literal — skip to avoid false matches
        if src[pos] == '"':
            j = pos + 1
            while j < len(src) and src[j] != '"':
                if src[j] == '\\':
                    j += 2
                else:
                    j += 1
            pos = j + 1
            continue

        pos += 1

    return comments


# =====================================================================
# Comment attachment
# =====================================================================

@dataclass
class _Attached:
    """Comments attached to positions in the formatted output."""
    # key = AST node start line; value = comments before that node
    before: dict[int, list[Comment]]
    # key = AST node start line; value = inline comment on that line
    inline: dict[int, Comment]
    # Comments before first declaration
    header: list[Comment]
    # Comments after last declaration
    footer: list[Comment]


def _attach_comments(
    comments: list[Comment],
    program: Program,
) -> _Attached:
    """Map comments to AST node positions."""
    if not comments:
        return _Attached(before={}, inline={}, header=[], footer=[])

    # Collect anchor lines from top-level declarations
    anchors: list[int] = []
    last_end = 0
    for tld in program.declarations:
        if tld.span:
            anchors.append(tld.span.line)
            if tld.span.end_line > last_end:
                last_end = tld.span.end_line
        # Interior anchors let comments inside function bodies attach
        # to the statement/expression they precede rather than falling
        # to the footer.  last_end stays top-level-only so that the
        # header/footer boundary is unaffected.
        if isinstance(tld.decl, FnDecl):
            _collect_interior_anchors(tld.decl, anchors)

    # Also consider module/import spans
    first_code_line = 0
    if program.module and program.module.span:
        first_code_line = program.module.span.line
        anchors.insert(0, first_code_line)
    if program.imports:
        for imp in program.imports:
            if imp.span:
                if first_code_line == 0:
                    first_code_line = imp.span.line
                anchors.insert(0, imp.span.line)
                if imp.span.end_line > last_end:
                    last_end = imp.span.end_line

    anchors.sort()

    header: list[Comment] = []
    footer: list[Comment] = []
    before: dict[int, list[Comment]] = {}
    inline: dict[int, Comment] = {}

    for c in comments:
        if c.inline:
            inline[c.line] = c
            continue

        # Find the nearest anchor AFTER this comment
        placed = False
        for anchor in anchors:
            if anchor > c.end_line:
                before.setdefault(anchor, []).append(c)
                placed = True
                break

        if not placed:
            if anchors and c.line <= (anchors[0] if anchors else 0):
                header.append(c)
            else:
                footer.append(c)

    return _Attached(before=before, inline=inline,
                     header=header, footer=footer)


def _collect_interior_anchors(node: object, anchors: list[int]) -> None:
    """Recursively collect span start lines from interior AST nodes.

    Walks into blocks, if branches, match arm blocks, handler bodies,
    and where functions to find every statement and result-expression
    position that the formatter emits on its own line.
    """
    if isinstance(node, Block):
        for stmt in node.statements:
            if stmt.span:
                anchors.append(stmt.span.line)
        if node.expr.span:
            anchors.append(node.expr.span.line)
        # Recurse into the result expression for nested multi-line forms
        _collect_interior_anchors(node.expr, anchors)
    elif isinstance(node, IfExpr):
        _collect_interior_anchors(node.then_branch, anchors)
        _collect_interior_anchors(node.else_branch, anchors)
    elif isinstance(node, MatchExpr):
        for arm in node.arms:
            _collect_interior_anchors(arm.body, anchors)
    elif isinstance(node, HandleExpr):
        _collect_interior_anchors(node.body, anchors)
    elif isinstance(node, FnDecl):
        _collect_interior_anchors(node.body, anchors)
        if node.where_fns:
            for wfn in node.where_fns:
                _collect_interior_anchors(wfn, anchors)


# =====================================================================
# Operator precedence
# =====================================================================

_PRECEDENCE: dict[BinOp, int] = {
    BinOp.PIPE: 1,
    BinOp.IMPLIES: 2,
    BinOp.OR: 3,
    BinOp.AND: 4,
    BinOp.EQ: 5,
    BinOp.NEQ: 5,
    BinOp.LT: 6,
    BinOp.GT: 6,
    BinOp.LE: 6,
    BinOp.GE: 6,
    BinOp.ADD: 7,
    BinOp.SUB: 7,
    BinOp.MUL: 8,
    BinOp.DIV: 8,
    BinOp.MOD: 8,
}

# Left-associative operators (right child needs parens at same prec)
_LEFT_ASSOC: set[BinOp] = {
    BinOp.PIPE, BinOp.OR, BinOp.AND,
    BinOp.ADD, BinOp.SUB,
    BinOp.MUL, BinOp.DIV, BinOp.MOD,
}

# Right-associative operators (left child needs parens at same prec)
_RIGHT_ASSOC: set[BinOp] = {BinOp.IMPLIES}

# Non-associative (both children need parens at same prec)
_NON_ASSOC: set[BinOp] = {
    BinOp.EQ, BinOp.NEQ,
    BinOp.LT, BinOp.GT, BinOp.LE, BinOp.GE,
}


def _needs_parens(child: Expr, parent_op: BinOp, side: str) -> bool:
    """Whether *child* needs parentheses when it appears as *side*
    ('left' or 'right') of *parent_op*."""
    if not isinstance(child, BinaryExpr):
        return False
    parent_prec = _PRECEDENCE[parent_op]
    child_prec = _PRECEDENCE[child.op]
    if child_prec < parent_prec:
        return True
    if child_prec > parent_prec:
        return False
    # Same precedence — depends on associativity
    if parent_op in _LEFT_ASSOC:
        return side == "right"
    if parent_op in _RIGHT_ASSOC:
        return side == "left"
    # Non-associative — always paren (shouldn't happen after parsing)
    return True


# =====================================================================
# Formatter
# =====================================================================

class Formatter:
    """Walk a Vera AST and emit canonically formatted source text."""

    def __init__(self, attached: _Attached) -> None:
        self._lines: list[str] = []
        self._indent: int = 0
        self._attached = attached

    # -- Output helpers -----------------------------------------------

    def _line(self, text: str) -> None:
        """Emit an indented line."""
        prefix = "  " * self._indent
        self._lines.append(prefix + text)

    def _raw(self, text: str) -> None:
        """Emit a line with no indentation."""
        self._lines.append(text)

    def _blank(self) -> None:
        """Emit a blank line."""
        self._lines.append("")

    def _indent_inc(self) -> None:
        self._indent += 1

    def _indent_dec(self) -> None:
        self._indent -= 1

    def _emit_comments(self, anchor: int) -> None:
        """Emit comments attached before the given anchor line."""
        comments = self._attached.before.get(anchor, [])
        for c in comments:
            for cline in c.text.split("\n"):
                self._line(cline.strip() if c.kind == "block" else cline.strip())

    def _emit_header_comments(self) -> None:
        for c in self._attached.header:
            for cline in c.text.split("\n"):
                self._raw(cline.rstrip())

    def _emit_footer_comments(self) -> None:
        for c in self._attached.footer:
            for cline in c.text.split("\n"):
                self._raw(cline.rstrip())

    # -- Program ------------------------------------------------------

    def format_program(self, prog: Program) -> str:
        """Format a complete program and return the source string."""
        self._emit_header_comments()

        if prog.module:
            self._emit_module(prog.module)

        if prog.imports:
            if prog.module:
                self._blank()
            for imp in prog.imports:
                self._emit_import(imp)

        first_decl = True
        for tld in prog.declarations:
            if first_decl:
                if prog.module or prog.imports:
                    self._blank()
                first_decl = False
            else:
                self._blank()

            # Emit comments before this declaration
            if tld.span:
                self._emit_comments(tld.span.line)
            self._emit_top_level(tld)

        self._emit_footer_comments()

        # Rule 10: file ends with a single newline
        result = "\n".join(self._lines)
        # Strip trailing whitespace on each line (Rule 9)
        result = "\n".join(line.rstrip() for line in result.split("\n"))
        # Ensure single trailing newline
        result = result.rstrip("\n") + "\n"
        return result

    # -- Module / imports ----------------------------------------------

    def _emit_module(self, mod: ModuleDecl) -> None:
        path = ".".join(mod.path)
        self._raw(f"module {path};")

    def _emit_import(self, imp: ImportDecl) -> None:
        path = ".".join(imp.path)
        if imp.names is not None:
            names = ", ".join(imp.names)
            self._raw(f"import {path}({names});")
        else:
            self._raw(f"import {path};")

    # -- Top-level declarations ----------------------------------------

    def _emit_top_level(self, tld: TopLevelDecl) -> None:
        decl = tld.decl
        vis = tld.visibility

        if isinstance(decl, FnDecl):
            self._emit_fn_decl(decl, vis)
        elif isinstance(decl, DataDecl):
            self._emit_data_decl(decl, vis)
        elif isinstance(decl, TypeAliasDecl):
            self._emit_type_alias(decl, vis)
        elif isinstance(decl, EffectDecl):
            self._emit_effect_decl(decl, vis)
        elif isinstance(decl, AbilityDecl):
            self._emit_ability_decl(decl, vis)

    # -- Function declarations -----------------------------------------

    def _emit_fn_decl(self, fn: FnDecl, vis: str | None) -> None:
        # Build signature line
        parts: list[str] = []
        if vis:
            parts.append(vis)

        if fn.forall_vars:
            vars_str = ", ".join(fn.forall_vars)
            if fn.forall_constraints:
                constraints_str = ", ".join(
                    f"{c.ability_name}<{c.type_var}>"
                    for c in fn.forall_constraints
                )
                parts.append(f"forall<{vars_str} where {constraints_str}>")
            else:
                parts.append(f"forall<{vars_str}>")

        parts.append("fn")
        parts.append(fn.name + self._fmt_signature(fn.params, fn.return_type))

        self._line(" ".join(parts))

        # Contract clauses — each on its own line, indented 2 spaces
        self._indent_inc()
        for c in fn.contracts:
            self._emit_contract(c)

        # Effects clause
        self._line(f"effects({self._fmt_effect_row(fn.effect)})")
        self._indent_dec()

        # Opening brace on its own line (function body convention)
        self._line("{")

        # Body
        self._indent_inc()
        self._emit_block_body(fn.body)
        self._indent_dec()

        # Closing brace
        self._line("}")

        # Where block
        if fn.where_fns:
            self._emit_where_block(fn.where_fns)

    def _emit_where_block(self, fns: tuple[FnDecl, ...]) -> None:
        self._line("where {")
        for i, fn in enumerate(fns):
            if i > 0:
                self._blank()
            self._indent_inc()
            self._emit_fn_decl(fn, None)
            self._indent_dec()
        self._line("}")

    def _fmt_signature(
        self,
        params: tuple[TypeExpr, ...],
        return_type: TypeExpr,
    ) -> str:
        """Format function signature: (@T1, @T2 -> @R)."""
        param_strs = ", ".join(self._fmt_param_type(p) for p in params)
        ret = self._fmt_param_type(return_type)
        if param_strs:
            return f"({param_strs} -> {ret})"
        return f"(-> {ret})"

    def _fmt_param_type(self, te: TypeExpr) -> str:
        """Format a type expression in parameter position (with @ prefix)."""
        return "@" + self._fmt_type_bare(te)

    def _fmt_type_bare(self, te: TypeExpr) -> str:
        """Format a type expression without @ prefix."""
        if isinstance(te, NamedType):
            if te.type_args:
                args = ", ".join(self._fmt_type_bare(a) for a in te.type_args)
                return f"{te.name}<{args}>"
            return te.name
        if isinstance(te, FnType):
            return self._fmt_fn_type(te)
        if isinstance(te, RefinementType):
            return self._fmt_refinement_type(te)
        return "?"  # pragma: no cover

    def _fmt_fn_type(self, ft: FnType) -> str:
        """Format a function type: fn(Params -> Return) effects(...)."""
        params = ", ".join(self._fmt_type_bare(p) for p in ft.params)
        ret = self._fmt_type_bare(ft.return_type)
        eff = self._fmt_effect_row(ft.effect)
        if params:
            return f"fn({params} -> {ret}) effects({eff})"
        return f"fn(-> {ret}) effects({eff})"

    def _fmt_refinement_type(self, rt: RefinementType) -> str:
        """Format a refinement type: { @Base | predicate }."""
        base = self._fmt_param_type(rt.base_type)
        pred = self._fmt_expr(rt.predicate)
        return f"{{ {base} | {pred} }}"

    # -- Data declarations ---------------------------------------------

    def _emit_data_decl(self, data: DataDecl, vis: str | None) -> None:
        parts: list[str] = []
        if vis:
            parts.append(vis)
        parts.append("data")

        name = data.name
        if data.type_params:
            tps = ", ".join(data.type_params)
            name += f"<{tps}>"
        parts.append(name)

        # Invariant
        inv_str = ""
        if data.invariant:
            inv_str = f" invariant({self._fmt_expr(data.invariant)})"

        header = " ".join(parts) + inv_str + " {"
        self._line(header)

        # Constructors — each on its own line, indented
        self._indent_inc()
        for i, ctor in enumerate(data.constructors):
            comma = "," if i < len(data.constructors) - 1 else ""
            if ctor.fields is not None:
                fields = ", ".join(self._fmt_type_bare(f) for f in ctor.fields)
                self._line(f"{ctor.name}({fields}){comma}")
            else:
                self._line(f"{ctor.name}{comma}")
        self._indent_dec()
        self._line("}")

    # -- Type alias declarations ---------------------------------------

    def _emit_type_alias(self, ta: TypeAliasDecl, vis: str | None) -> None:
        parts: list[str] = []
        if vis:
            parts.append(vis)
        parts.append("type")

        name = ta.name
        if ta.type_params:
            tps = ", ".join(ta.type_params)
            name += f"<{tps}>"
        parts.append(name)

        type_str = self._fmt_type_for_alias(ta.type_expr)
        self._line(f"{' '.join(parts)} = {type_str};")

    def _fmt_type_for_alias(self, te: TypeExpr) -> str:
        """Format a type expr in alias RHS position (special rules)."""
        if isinstance(te, FnType):
            return self._fmt_fn_type(te)
        if isinstance(te, RefinementType):
            base = self._fmt_param_type(te.base_type)
            pred = self._fmt_expr(te.predicate)
            return f"{{ {base} | {pred} }}"
        return self._fmt_type_bare(te)

    # -- Effect declarations -------------------------------------------

    def _emit_effect_decl(self, eff: EffectDecl, vis: str | None) -> None:
        parts: list[str] = []
        if vis:
            parts.append(vis)
        parts.append("effect")

        name = eff.name
        if eff.type_params:
            tps = ", ".join(eff.type_params)
            name += f"<{tps}>"
        parts.append(name)

        self._line(" ".join(parts) + " {")

        self._indent_inc()
        for op in eff.operations:
            self._emit_op_decl(op)
        self._indent_dec()
        self._line("}")

    def _emit_op_decl(self, op: OpDecl) -> None:
        params = ", ".join(self._fmt_type_bare(p) for p in op.param_types)
        ret = self._fmt_type_bare(op.return_type)
        if params:
            self._line(f"op {op.name}({params} -> {ret});")
        else:
            self._line(f"op {op.name}(-> {ret});")

    # -- Ability declarations ------------------------------------------

    def _emit_ability_decl(self, ab: AbilityDecl, vis: str | None) -> None:
        parts: list[str] = []
        if vis:
            parts.append(vis)
        parts.append("ability")

        name = ab.name
        if ab.type_params:
            tps = ", ".join(ab.type_params)
            name += f"<{tps}>"
        parts.append(name)

        self._line(" ".join(parts) + " {")

        self._indent_inc()
        for op in ab.operations:
            self._emit_op_decl(op)
        self._indent_dec()
        self._line("}")

    # -- Contracts -----------------------------------------------------

    def _emit_contract(self, c: Contract) -> None:
        if isinstance(c, Requires):
            self._line(f"requires({self._fmt_expr(c.expr)})")
        elif isinstance(c, Ensures):
            self._line(f"ensures({self._fmt_expr(c.expr)})")
        elif isinstance(c, Decreases):
            exprs = ", ".join(self._fmt_expr(e) for e in c.exprs)
            self._line(f"decreases({exprs})")
        elif isinstance(c, Invariant):
            self._line(f"invariant({self._fmt_expr(c.expr)})")

    # -- Effect rows ---------------------------------------------------

    def _fmt_effect_row(self, eff: EffectRow) -> str:
        if isinstance(eff, PureEffect):
            return "pure"
        if isinstance(eff, EffectSet):
            refs = ", ".join(self._fmt_effect_ref(r) for r in eff.effects)
            return f"<{refs}>"
        return "?"  # pragma: no cover

    def _fmt_effect_ref(self, ref: EffectRefNode) -> str:
        if isinstance(ref, EffectRef):
            if ref.type_args:
                args = ", ".join(self._fmt_type_bare(a) for a in ref.type_args)
                return f"{ref.name}<{args}>"
            return ref.name
        if isinstance(ref, QualifiedEffectRef):
            base = f"{ref.module}.{ref.name}"
            if ref.type_args:
                args = ", ".join(self._fmt_type_bare(a) for a in ref.type_args)
                return f"{base}<{args}>"
            return base
        return "?"  # pragma: no cover

    # -- Block body (statements + expression) --------------------------

    def _emit_block_body(self, block: Block) -> None:
        """Emit the interior of a block (statements then expression)."""
        for stmt in block.statements:
            if stmt.span:
                self._emit_comments(stmt.span.line)
            self._emit_stmt(stmt)
        if block.expr.span:
            self._emit_comments(block.expr.span.line)
        self._emit_block_expr(block.expr)

    def _emit_block_expr(self, expr: Expr) -> None:
        """Emit a block's result expression (may be multi-line)."""
        if isinstance(expr, IfExpr):
            self._emit_if(expr)
        elif isinstance(expr, MatchExpr):
            self._emit_match(expr)
        elif isinstance(expr, HandleExpr):
            self._emit_handle(expr)
        elif isinstance(expr, Block):
            # Nested block
            self._line("{")
            self._indent_inc()
            self._emit_block_body(expr)
            self._indent_dec()
            self._line("}")
        else:
            self._line(self._fmt_expr(expr))

    # -- Statements ----------------------------------------------------

    def _emit_stmt(self, stmt: Stmt) -> None:
        if isinstance(stmt, LetStmt):
            te = self._fmt_param_type(stmt.type_expr)
            val = self._fmt_expr(stmt.value)
            self._line(f"let {te} = {val};")
        elif isinstance(stmt, LetDestruct):
            bindings = ", ".join(
                self._fmt_param_type(b) for b in stmt.type_bindings
            )
            val = self._fmt_expr(stmt.value)
            self._line(f"let {stmt.constructor}<{bindings}> = {val};")
        elif isinstance(stmt, ExprStmt):
            self._line(f"{self._fmt_expr(stmt.expr)};")

    # -- Multi-line expressions ----------------------------------------

    def _emit_if(self, expr: IfExpr) -> None:
        cond = self._fmt_expr(expr.condition)
        self._line(f"if {cond} then {{")
        self._indent_inc()
        self._emit_block_body(expr.then_branch)
        self._indent_dec()
        self._line("} else {")
        self._indent_inc()
        self._emit_block_body(expr.else_branch)
        self._indent_dec()
        self._line("}")

    def _emit_match(self, expr: MatchExpr) -> None:
        scrut = self._fmt_expr(expr.scrutinee)
        self._line(f"match {scrut} {{")
        self._indent_inc()
        for i, arm in enumerate(expr.arms):
            comma = "," if i < len(expr.arms) - 1 else ""
            pat = self._fmt_pattern(arm.pattern)
            if isinstance(arm.body, Block) and arm.body.statements:
                # Multi-statement block: emit multi-line with braces
                self._line(f"{pat} -> {{")
                self._indent_inc()
                self._emit_block_body(arm.body)
                self._indent_dec()
                self._line(f"}}{comma}")
            else:
                body = self._fmt_expr(arm.body)
                self._line(f"{pat} -> {body}{comma}")
        self._indent_dec()
        self._line("}")

    def _emit_handle(self, expr: HandleExpr) -> None:
        eff = self._fmt_effect_ref(expr.effect)
        state_str = ""
        if expr.state:
            st = expr.state
            te = self._fmt_param_type(st.type_expr)
            init = self._fmt_expr(st.init_expr)
            state_str = f"({te} = {init})"

        self._line(f"handle[{eff}]{state_str} {{")
        self._indent_inc()
        for i, clause in enumerate(expr.clauses):
            comma = "," if i < len(expr.clauses) - 1 else ""
            self._emit_handler_clause(clause, comma)
        self._indent_dec()
        self._line("} in {")
        self._indent_inc()
        self._emit_block_body(expr.body)
        self._indent_dec()
        self._line("}")

    def _emit_handler_clause(self, clause: HandlerClause, comma: str) -> None:
        params = ", ".join(
            self._fmt_param_type(p) for p in clause.params
        )
        body = self._fmt_expr(clause.body)

        with_str = ""
        if clause.state_update:
            te = self._fmt_param_type(clause.state_update[0])
            val = self._fmt_expr(clause.state_update[1])
            with_str = f" with {te} = {val}"

        self._line(
            f"{clause.op_name}({params}) -> "
            f"{{ {body} }}{with_str}{comma}"
        )

    # -- Inline expression formatting ----------------------------------

    def _fmt_expr(self, expr: Expr) -> str:
        """Format an expression as a single-line string."""
        if isinstance(expr, IntLit):
            return str(expr.value)
        if isinstance(expr, FloatLit):
            return self._fmt_float(expr.value)
        if isinstance(expr, BoolLit):
            return "true" if expr.value else "false"
        if isinstance(expr, StringLit):
            return f'"{_encode_string_escapes(expr.value)}"'
        if isinstance(expr, InterpolatedString):
            chunks: list[str] = []
            for part in expr.parts:
                if isinstance(part, str):
                    chunks.append(_encode_string_escapes(part))
                else:
                    chunks.append(f"\\({self._fmt_expr(part)})")
            return '"' + "".join(chunks) + '"'
        if isinstance(expr, UnitLit):
            return "()"
        if isinstance(expr, HoleExpr):
            return "?"
        if isinstance(expr, ArrayLit):
            elems = ", ".join(self._fmt_expr(e) for e in expr.elements)
            return f"[{elems}]"

        # Slot references
        if isinstance(expr, SlotRef):
            base = expr.type_name
            if expr.type_args:
                args = ", ".join(
                    self._fmt_type_bare(a) for a in expr.type_args
                )
                base = f"{base}<{args}>"
            return f"@{base}.{expr.index}"
        if isinstance(expr, ResultRef):
            base = expr.type_name
            if expr.type_args:
                args = ", ".join(
                    self._fmt_type_bare(a) for a in expr.type_args
                )
                base = f"{base}<{args}>"
            return f"@{base}.result"

        # Binary / unary / index
        if isinstance(expr, BinaryExpr):
            return self._fmt_binary(expr)
        if isinstance(expr, UnaryExpr):
            return self._fmt_unary(expr)
        if isinstance(expr, IndexExpr):
            coll = self._fmt_expr(expr.collection)
            idx = self._fmt_expr(expr.index)
            return f"{coll}[{idx}]"

        # Calls
        if isinstance(expr, FnCall):
            args = ", ".join(self._fmt_expr(a) for a in expr.args)
            return f"{expr.name}({args})"
        if isinstance(expr, ConstructorCall):
            args = ", ".join(self._fmt_expr(a) for a in expr.args)
            return f"{expr.name}({args})"
        if isinstance(expr, NullaryConstructor):
            return expr.name
        if isinstance(expr, QualifiedCall):
            args = ", ".join(self._fmt_expr(a) for a in expr.args)
            return f"{expr.qualifier}.{expr.name}({args})"
        if isinstance(expr, ModuleCall):
            path = ".".join(expr.path)
            args = ", ".join(self._fmt_expr(a) for a in expr.args)
            return f"{path}::{expr.name}({args})"

        # Lambda
        if isinstance(expr, AnonFn):
            return self._fmt_anon_fn(expr)

        # Control flow (inline form for use inside expressions)
        if isinstance(expr, IfExpr):
            return self._fmt_if_inline(expr)
        if isinstance(expr, MatchExpr):
            return self._fmt_match_inline(expr)
        if isinstance(expr, HandleExpr):
            return self._fmt_handle_inline(expr)
        if isinstance(expr, Block):
            return self._fmt_block_inline(expr)

        # Contract expressions
        if isinstance(expr, OldExpr):
            return f"old({self._fmt_effect_ref(expr.effect_ref)})"
        if isinstance(expr, NewExpr):
            return f"new({self._fmt_effect_ref(expr.effect_ref)})"
        if isinstance(expr, AssertExpr):
            return f"assert({self._fmt_expr(expr.expr)})"
        if isinstance(expr, AssumeExpr):
            return f"assume({self._fmt_expr(expr.expr)})"

        # Quantifiers
        if isinstance(expr, ForallExpr):
            return self._fmt_quantifier("forall", expr)
        if isinstance(expr, ExistsExpr):
            return self._fmt_quantifier("exists", expr)

        return "<expr>"  # pragma: no cover

    def _fmt_float(self, value: float) -> str:
        """Format a float literal canonically."""
        s = repr(value)
        # repr gives things like 3.14, 100.0, inf, etc.
        # Ensure it always has a decimal point
        if "." not in s and "e" not in s.lower() and "inf" not in s.lower():
            s = s + ".0"  # pragma: no cover
        return s

    def _fmt_binary(self, expr: BinaryExpr) -> str:
        left = self._fmt_expr(expr.left)
        right = self._fmt_expr(expr.right)

        if _needs_parens(expr.left, expr.op, "left"):
            left = f"({left})"
        if _needs_parens(expr.right, expr.op, "right"):
            right = f"({right})"

        return f"{left} {expr.op.value} {right}"

    def _fmt_unary(self, expr: UnaryExpr) -> str:
        operand = self._fmt_expr(expr.operand)

        # Need parens if operand is binary or is a unary neg (avoid --)
        needs = False
        if isinstance(expr.operand, BinaryExpr):
            needs = True
        elif (isinstance(expr.operand, UnaryExpr)
              and expr.op == UnaryOp.NEG
              and expr.operand.op == UnaryOp.NEG):
            needs = True

        if needs:
            operand = f"({operand})"

        if expr.op == UnaryOp.NEG:
            return f"-{operand}"
        return f"!{operand}"

    def _fmt_anon_fn(self, fn: AnonFn) -> str:
        sig = self._fmt_signature(fn.params, fn.return_type)
        eff = self._fmt_effect_row(fn.effect)
        body = self._fmt_expr(fn.body.expr) if not fn.body.statements else (
            self._fmt_block_inline(fn.body)
        )
        return f"fn{sig} effects({eff}) {{ {body} }}"

    def _fmt_if_inline(self, expr: IfExpr) -> str:
        """Format if-then-else as inline (for use inside other expressions)."""
        cond = self._fmt_expr(expr.condition)
        then_body = self._fmt_block_inline(expr.then_branch)
        else_body = self._fmt_block_inline(expr.else_branch)
        return f"if {cond} then {{ {then_body} }} else {{ {else_body} }}"

    def _fmt_match_inline(self, expr: MatchExpr) -> str:
        """Format match as inline."""
        scrut = self._fmt_expr(expr.scrutinee)
        arms = ", ".join(
            f"{self._fmt_pattern(a.pattern)} -> {self._fmt_arm_body(a.body)}"
            for a in expr.arms
        )
        return f"match {scrut} {{ {arms} }}"

    def _fmt_arm_body(self, body: Expr) -> str:
        """Format a match arm body, wrapping multi-statement blocks in braces."""
        if isinstance(body, Block) and body.statements:
            return f"{{ {self._fmt_block_inline(body)} }}"
        return self._fmt_expr(body)

    def _fmt_handle_inline(self, expr: HandleExpr) -> str:
        """Format handle as inline (shouldn't normally be needed)."""
        # This is a fallback — handles are typically multi-line
        eff = self._fmt_effect_ref(expr.effect)
        return f"handle[{eff}] {{ ... }}"  # pragma: no cover

    def _fmt_block_inline(self, block: Block) -> str:
        """Format a block's body inline (no braces)."""
        parts: list[str] = []
        for stmt in block.statements:
            if isinstance(stmt, LetStmt):
                te = self._fmt_param_type(stmt.type_expr)
                val = self._fmt_expr(stmt.value)
                parts.append(f"let {te} = {val};")
            elif isinstance(stmt, LetDestruct):
                bindings = ", ".join(
                    self._fmt_param_type(b) for b in stmt.type_bindings
                )
                val = self._fmt_expr(stmt.value)
                parts.append(f"let {stmt.constructor}<{bindings}> = {val};")
            elif isinstance(stmt, ExprStmt):
                parts.append(f"{self._fmt_expr(stmt.expr)};")
        parts.append(self._fmt_expr(block.expr))
        return " ".join(parts)

    def _fmt_quantifier(
        self,
        kind: str,
        expr: ForallExpr | ExistsExpr,
    ) -> str:
        binding = self._fmt_param_type(expr.binding_type)
        domain = self._fmt_expr(expr.domain)
        pred = self._fmt_anon_fn(expr.predicate)
        return f"{kind}({binding}, {domain}, {pred})"

    # -- Patterns ------------------------------------------------------

    def _fmt_pattern(self, pat: Pattern) -> str:
        if isinstance(pat, ConstructorPattern):
            subs = ", ".join(self._fmt_pattern(s) for s in pat.sub_patterns)
            return f"{pat.name}({subs})"
        if isinstance(pat, NullaryPattern):
            return pat.name
        if isinstance(pat, BindingPattern):
            return self._fmt_param_type(pat.type_expr)
        if isinstance(pat, WildcardPattern):
            return "_"
        if isinstance(pat, IntPattern):
            return str(pat.value)
        if isinstance(pat, StringPattern):
            return f'"{_encode_string_escapes(pat.value)}"'
        if isinstance(pat, BoolPattern):
            return "true" if pat.value else "false"
        return "_"  # pragma: no cover


# =====================================================================
# Public API
# =====================================================================

def format_source(source: str, file: str | None = None) -> str:
    """Format Vera source code to canonical form.

    Parses *source*, formats the AST, re-inserts comments,
    and returns the canonically-formatted string.

    Raises ``VeraError`` on parse failure.
    """
    comments = extract_comments(source)
    if file is not None:
        tree = parse_file(file)
    else:
        tree = vera_parse(source)
    program = transform(tree)
    attached = _attach_comments(comments, program)
    fmt = Formatter(attached)
    return fmt.format_program(program)
