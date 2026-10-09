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

import unicodedata
from collections import Counter
from dataclasses import dataclass
from decimal import Decimal

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
    IfExpr,
    ImportDecl,
    IndexExpr,
    InterpolatedString,
    IntLit,
    IntPattern,
    Invariant,
    LetDestruct,
    LetStmt,
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
from vera.lexical import CommentKind, scan_comments
from vera.parser import parse as vera_parse
from vera.transform import transform

_STRING_ENCODE_MAP = {
    "\\": "\\\\",
    '"': '\\"',
    "\n": "\\n",
    "\t": "\\t",
    "\r": "\\r",
    "\0": "\\0",
}

# Unicode general categories whose members carry no visible glyph of their
# own: controls, format characters (zero-width joiners, bidi overrides),
# surrogates, private use, unassigned, and the line/paragraph separators.
_INVISIBLE_CATEGORIES = frozenset({"Cc", "Cf", "Cs", "Co", "Cn", "Zl", "Zp"})


def _is_unreadable(ch: str) -> bool:
    """Whether *ch* must be escaped because it cannot be read as itself.

    Rule 1.8 is about a canonical form a reader can trust, and a
    character that renders as nothing — a zero-width space, a bidi
    override, an unassigned code point — defeats that: two literals that
    look identical are not, and the difference is invisible in review.
    Everything printable stays literal, including non-ASCII: ``café`` and
    an emoji read fine as themselves and escaping them would make the
    canonical form *less* legible than the source.

    Space-separator (``Zs``) is split: the ASCII space is the ordinary
    one and stays, while a no-break or hair space is a look-alike that
    only an escape distinguishes.
    """
    category = unicodedata.category(ch)
    if category in _INVISIBLE_CATEGORIES:
        return True
    return category == "Zs" and ch != " "


def _encode_string_escapes(s: str) -> str:
    """Re-encode special characters as Vera escape sequences."""
    out: list[str] = []
    for c in s:
        mapped = _STRING_ENCODE_MAP.get(c)
        if mapped is not None:
            out.append(mapped)
        elif _is_unreadable(c):
            # Uppercase hex, at least four digits: `\u{200B}` matches the
            # spelling the spec's escape table uses, and the decoder
            # accepts 1-6 digits so a wider code point simply gets more.
            out.append(f"\\u{{{ord(c):04X}}}")
        else:
            out.append(c)
    return "".join(out)


def blank_source_lines(source: str) -> frozenset[int]:
    """The 1-based line numbers in *source* that hold only whitespace.

    A blank line is the one piece of a program's layout the AST cannot
    record: two statements separated by a paragraph break parse to
    exactly the same tree as two written back to back.  So the formatter
    is given the source's blank lines directly, and reproduces a gap only
    where there was one -- the alternative is to strip every gap (which
    is what deleted the paragraph breaks from `examples/file_io.vera`)
    or to invent one everywhere (which would be worse).

    Lines inside a block comment are not separators: a `{- -}` spanning
    an empty line is one comment, not a paragraph break, so any line a
    comment's span covers is excluded from the map.  (A raw whitespace
    scan read that interior line as a gap and manufactured a blank the
    author never wrote.)
    """
    covered: set[int] = set()
    for span in scan_comments(source):
        start_line = source.count("\n", 0, span.start) + 1
        end_line = source.count("\n", 0, span.end) + 1
        covered.update(range(start_line, end_line + 1))
    return frozenset(
        i for i, line in enumerate(source.split("\n"), start=1)
        if not line.strip() and i not in covered
    )


# =====================================================================
# Comment extraction
# =====================================================================

@dataclass
class Comment:
    """A comment extracted from source text."""
    kind: CommentKind
    text: str       # Full text including delimiters
    line: int       # 1-based start line
    column: int     # 1-based start column
    end_line: int   # 1-based end line
    inline: bool    # True if code precedes this comment on the same line
    paren_depth: int = 0  # see lexical.CommentSpan.paren_depth


def extract_comments(source: str) -> list[Comment]:
    """Extract all comments from Vera source, preserving positions.

    The scan itself lives in :mod:`vera.lexical`, shared with the
    parser's pre-lex pass, so the two cannot disagree about where a
    comment starts or ends.  That disagreement is exactly what caused
    #1112: this extractor counted block-comment nesting depth (and the
    suite asserted it) while the grammar's regex closed at the first
    ``-}``, so identical text was one comment to ``vera fmt`` and a
    syntax error to ``vera check``.
    """
    comments: list[Comment] = []
    for span in scan_comments(source):
        line_start = source.rfind("\n", 0, span.start) + 1
        comments.append(Comment(
            kind=span.kind,
            text=source[span.start:span.end],
            line=source.count("\n", 0, span.start) + 1,
            column=span.start - line_start + 1,
            end_line=source.count("\n", 0, span.end) + 1,
            inline=source[line_start:span.start].strip() != "",
            paren_depth=span.paren_depth,
        ))
    return comments


def _flatten_comment(comment: Comment) -> str:
    """A comment's text as one physical line.

    A `{- -}` or `/* */` may span lines while still being inline.  Emitting
    it verbatim puts a newline inside one output line, and the
    continuation survives the final join carrying its *original* source
    indentation — a physically misindented line, against spec 1.8 rule 1.
    Collapse only when it spans lines, so a single-line comment keeps its
    internal spacing.
    """
    text = comment.text
    return text.strip() if "\n" not in text else " ".join(text.split())


def _annotation_suffix(label: str | None) -> str:
    """Render a binding's annotation label, or nothing at all.

    The label comes from the AST, where it kept whatever line structure it
    had in source, so it needs the same flattening as a claimed comment —
    this path splices straight into a signature line.
    """
    if not label:
        return ""
    return f" /* {' '.join(label.split())} */"


# =====================================================================
# Comment attachment
# =====================================================================

@dataclass
class _Attached:
    """Comments attached to positions in the formatted output."""
    # key = AST node start line; value = comments before that node
    before: dict[int, list[Comment]]
    # Comments with code before them on their line, in source order.  Held
    # as a flat list rather than keyed by line because placement is decided
    # at emission time: each is claimed by the innermost construct whose
    # span contains it.  A line-keyed store could hold only one per line,
    # which loses a second trailing comment outright (#1123).
    inline: list[Comment]
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
        return _Attached(before={}, inline=[], header=[], footer=[])

    # Collect anchor lines from top-level declarations
    anchors: list[int] = []
    last_end = 0
    for tld in program.declarations:
        if tld.span:
            anchors.append(tld.span.line)
            if tld.span.end_line > last_end:
                last_end = tld.span.end_line
        # Interior anchors let comments inside declarations attach to the
        # item they precede rather than falling to the footer.  last_end stays
        # top-level-only so that the header/footer boundary is unaffected.
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
    inline: list[Comment] = []

    for c in comments:
        if c.inline:
            inline.append(c)
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


def _needs_own_lines(node: object) -> bool:
    """True for constructs whose braces rule 2 puts on their own lines.

    `match`, `if` and `handle` all emit a brace that must close on a
    line of its own aligned with the construct, so none of them may be
    flattened into a containing line.
    """
    return isinstance(node, (MatchExpr, IfExpr, HandleExpr))


def _unwrap_redundant_block(node: Expr) -> Expr:
    """Strip a block that only wraps a single multi-line construct.

    `{ match ... }` and `match ...` are two textual forms of one
    construct, which rule 1.8 forbids; the bare form is canonical.
    The wrapper matters because a block holding no statements keeps its
    content in `expr`, so a `statements`-only test reads it as empty
    and flattens the construct inside it.
    """
    if (
        isinstance(node, Block)
        and not node.statements
        and _needs_own_lines(node.expr)
    ):
        return node.expr
    return node


def _stmt_value(stmt: Stmt) -> Expr | None:
    """The expression a statement holds, whatever kind it is.

    All three statement kinds put an expression in value position, and
    all three emit it through the same rule-2 path, so both the anchor
    walk and the emitter need one answer rather than three branches
    that can drift apart.
    """
    if isinstance(stmt, LetStmt):
        return stmt.value
    if isinstance(stmt, LetDestruct):
        return stmt.value
    if isinstance(stmt, ExprStmt):
        return stmt.expr
    return None  # pragma: no cover - Stmt has no fourth kind


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
            # And into whatever the statement holds.  Only the
            # statement's own start line was an anchor, so every
            # position *inside* a statement — a match arm, a handler
            # clause, a branch's statements — was invisible here and a
            # comment written above one fell through to the next
            # statement, documenting something it was not written for.
            _collect_interior_anchors(_stmt_value(stmt), anchors)
        if node.expr.span:
            anchors.append(node.expr.span.line)
        # Recurse into the result expression for nested multi-line forms
        _collect_interior_anchors(node.expr, anchors)
    elif isinstance(node, IfExpr):
        # The if's own line is an anchor for the same reason as the
        # match below: without it a comment above a next-line `if` in
        # value position attached to the first anchor *inside* the
        # construct and was emitted in the then-branch.
        if node.span:
            anchors.append(node.span.line)
        _collect_interior_anchors(node.then_branch, anchors)
        _collect_interior_anchors(node.else_branch, anchors)
    elif isinstance(node, MatchExpr):
        # The match's own line is an anchor too: a comment above a
        # nested `match` used directly as an arm body would otherwise
        # fall through to that match's first arm, silently changing
        # what it appears to document.
        if node.span:
            anchors.append(node.span.line)
        for arm in node.arms:
            # The arm itself is an anchor, not just its body: a comment
            # above `Red -> 1` precedes the arm, and without this the
            # innermost span containing it is the match, so every arm
            # comment piled up together at the top (#1136).
            if arm.span:
                anchors.append(arm.span.line)
            # The body's own line too: `0 ->` followed by a next-line
            # body is a position a comment can precede, and without
            # this anchor that comment drifted to the NEXT arm — or,
            # for the last arm, out of the function entirely.
            if arm.body.span:
                anchors.append(arm.body.span.line)
            _collect_interior_anchors(arm.body, anchors)
    elif isinstance(node, HandleExpr):
        # The handle's own line, mirroring MatchExpr/IfExpr above.
        if node.span:
            anchors.append(node.span.line)
        for clause in node.clauses:
            # Same as a match arm: without an anchor the innermost span
            # containing a clause comment is the handle, so every one
            # fell through to the declaration backstop (#1136).
            if clause.span:
                anchors.append(clause.span.line)
            # And into the clause body.  A clause renders on a single
            # line, so emission never visits these positions itself;
            # `_emit_handle` drains them at the owning clause, which
            # keeps a comment inside a multi-line body on the clause
            # it documents instead of migrating to the next one.
            if clause.body.span:
                anchors.append(clause.body.span.line)
            _collect_interior_anchors(clause.body, anchors)
        _collect_interior_anchors(node.body, anchors)
    elif isinstance(node, FnDecl):
        # Contract and effect clauses each occupy their own line
        # (rule 7), so each is a position a comment can precede.  Only
        # the declaration's span used to cover the gap between the
        # signature and `requires(`, which sent those comments to the
        # top of the body (#1136).
        for contract in node.contracts:
            if contract.span:
                anchors.append(contract.span.line)
        if node.effect.span:
            anchors.append(node.effect.span.line)
        _collect_interior_anchors(node.body, anchors)
        if node.where_fns:
            # The `where` keyword line itself, before the functions
            # inside it: without this anchor the nearest position after a
            # comment above `where {` is the first where-function, so the
            # comment was pulled into the block and re-indented (#1136).
            if node.where_span:
                anchors.append(node.where_span.line)
            for wfn in node.where_fns:
                # And each function inside it, or a comment above one
                # attaches to its first contract clause instead.
                if wfn.span:
                    anchors.append(wfn.span.line)
                _collect_interior_anchors(wfn, anchors)
    elif isinstance(node, DataDecl):
        for constructor in node.constructors:
            if constructor.span:
                anchors.append(constructor.span.line)
    elif isinstance(node, (EffectDecl, AbilityDecl)):
        for operation in node.operations:
            if operation.span:
                anchors.append(operation.span.line)


# =====================================================================
# Operator precedence
# =====================================================================

#: A piped call (`a |> f(b)`, a call whose `piped` is set) prints as the
#: loosest operator of all.
_PIPE_PRECEDENCE = 1

_PRECEDENCE: dict[BinOp, int] = {
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
    BinOp.OR, BinOp.AND,
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

# Node kinds that bind at least as tightly as postfix indexing, and so
# may stand as an `IndexExpr` collection without parentheses.  Anything
# else — an operator expression, control flow, a lambda, a block —
# must be re-wrapped: indexing is the tightest postfix level, so
# `(x |> f())[0]` emitted without its parens reparses as
# `x |> (f()[0])`, a different program.  A piped call is a call node that
# prints as an operator expression, so it is re-wrapped too (`_is_pipe`).
_POSTFIX_SAFE = (
    IntLit, FloatLit, BoolLit, StringLit, InterpolatedString, UnitLit,
    ArrayLit, SlotRef, ResultRef, FnCall, ConstructorCall,
    NullaryConstructor, QualifiedCall, ModuleCall, IndexExpr, HoleExpr,
    OldExpr, NewExpr, AssertExpr, AssumeExpr, ForallExpr, ExistsExpr,
)


#: The call forms a pipe can name (spec §4.11.2).
_CALL_FORMS = (FnCall, ConstructorCall, QualifiedCall, ModuleCall)


def _is_pipe(expr: Expr) -> bool:
    """Whether *expr* is a call written as a pipe, `args[0] |> f(...)`."""
    return isinstance(expr, _CALL_FORMS) and expr.piped and bool(expr.args)


def _needs_parens(child: Expr, parent_op: BinOp, side: str, *,
                  pipes: bool = True) -> bool:
    """Whether *child* needs parentheses when it appears as *side*
    ('left' or 'right') of *parent_op*.  *pipes* says whether a piped call
    prints as the pipe (see :meth:`Formatter._shows_pipe`)."""
    if pipes and _is_pipe(child):
        # Looser than every binary operator: `(a |> f()) + 1`.
        return _PIPE_PRECEDENCE < _PRECEDENCE[parent_op]
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

    def __init__(
        self,
        attached: _Attached,
        blank_lines: frozenset[int] = frozenset(),
        structural: bool = False,
    ) -> None:
        self._lines: list[str] = []
        self._indent: int = 0
        self._attached = attached
        # STRUCTURAL mode (#1238 round 2): render for DISCRIMINATION rather
        # than for canonical form.  Two sites below choose the canonical
        # spelling between two AST shapes the CHECKER holds apart — an arm
        # body's redundant block wrapper, and a handler clause's braces —
        # and picking one erases the distinction.  That is right for
        # `vera fmt`, whose whole job is to pick, and wrong for
        # `vera.types.structural_type_key`, where the rendering NAMES a
        # State cell: two predicates rendering alike is two cells sharing
        # one host cell behind a check that typed them apart (#1218's
        # failure mode, through the renderer that fixed it).  The converse
        # holds for a piped call: the `piped` flag is spelling, outside node
        # equality, so the checker holds the two spellings of a call to be
        # one predicate, and structural mode prints the call either way
        # (`_shows_pipe`).  Set only by :func:`format_expr_canonical`;
        # `format_source` never turns it on, so canonical output is
        # untouched.
        self._structural = structural
        # Source lines holding only whitespace, from
        # :func:`blank_source_lines`.  Defaulted so a caller that has an
        # AST but no text still formats -- it simply gets no gaps, which
        # is the behaviour that predates this.
        self._blank_lines = blank_lines
        # Identities of inline comments already placed.  Inner
        # constructs finish emitting first, so claiming greedily gives
        # each comment to the innermost construct that contains it.
        self._claimed_inline: set[int] = set()

    # -- Output helpers -----------------------------------------------

    def _line(self, text: str) -> None:
        """Emit an indented line."""
        prefix = "  " * self._indent
        self._lines.append(prefix + text)

    def _raw(self, text: str) -> None:
        """Emit a line with no indentation."""
        self._lines.append(text)

    def _blank(self) -> None:
        """Emit a blank line, unless the output already ends in one.

        Three paths reproduce a gap -- the comment emitter for the space
        *below* a comment, the block emitter for the space *above* one,
        and the declaration loop's unconditional separator.  As written
        none of them can land back to back, because the comment they
        bracket always sits between; clamping here is what makes rule
        13's "at most one" a property of the emitter rather than of an
        argument about its callers, so a fourth caller cannot break it.
        Nothing may open the output with a blank either.
        """
        if not self._lines or not self._lines[-1].strip():
            return
        self._lines.append("")

    def _leading_source_line(self, span_line: int) -> int:
        """The first source line emitted for a node starting at *span_line*.

        Comments attached above the node are emitted before it, so the
        gap separating it from what precedes it sits above the *comment
        block*, not above the node itself.
        """
        comments = self._attached.before.get(span_line, ())
        return min((c.line for c in comments), default=span_line)

    def _blank_if_separated(self, node: object) -> None:
        """Reproduce a single blank line the source held above *node*.

        Only where the source had one: a gap between statements is a
        paragraph break the author wrote, and neither keeping every gap
        nor discarding every gap can be recovered from the AST, which
        records no separation at all (rule 13).
        """
        span = getattr(node, "span", None)
        if span is None:
            return
        if self._leading_source_line(span.line) - 1 in self._blank_lines:
            self._blank()

    def _indent_inc(self) -> None:
        self._indent += 1

    def _indent_dec(self) -> None:
        self._indent -= 1

    def _emit_comments(self, anchor: int) -> None:
        """Emit comments attached before the given anchor line.

        A comment the source separated from what follows it keeps exactly
        one blank line of separation, however many it had: a header block
        held off its declaration reads as a header, and glued on it reads
        as a remark about the first line.  The gap is only reproduced
        when there was one in source, and never for a comment sharing the
        anchor's line, where "after the comment" is still the same line.
        """
        # Consume, don't peek: two anchors can collapse onto one
        # line after reformatting (an arm and the nested match it
        # holds), and a non-consuming read emits the comment once
        # per anchor — duplicating it on the second pass.
        comments = self._attached.before.pop(anchor, [])
        for c in comments:
            for cline in c.text.split("\n"):
                self._line(cline.strip())
            # The gap *below* the comment, read from the same source map
            # as the gap *above* it (`_blank_if_separated`).  The two are
            # halves of one rule rather than two mechanisms, and neither
            # needs to know about the other: the comment itself always
            # lands between them, so they cannot stack.  Past the end of
            # the file the line is simply absent from the map, so a
            # trailing gap reproduces nothing.  `end_line < anchor`
            # restates the attachment invariant -- `_attach_comments`
            # files a comment only under an anchor strictly below it, so
            # a comment sharing the anchor's line, where "after the
            # comment" is still that line, cannot reach here.
            if c.end_line < anchor and c.end_line + 1 in self._blank_lines:
                self._blank()

    def _claim_inline(
        self,
        node: object,
        upper: tuple[int, int] | None = None,
    ) -> None:
        """Append inline comments inside ``node``'s span to its last line.

        Called immediately after a construct is emitted, so
        ``self._lines[-1]`` is that construct's final output line.
        Because nested constructs are emitted -- and so claim -- first,
        a comment ends up on the innermost construct containing it,
        which is a fixed point: re-formatting finds it already trailing
        that construct and leaves it there.
        """
        span = getattr(node, "span", None)
        if span is None:
            return
        self._claim_inline_range(span.line, span.end_line, upper)

    def _suppress_signature_labels(
        self,
        start: int,
        end: int,
        consumed: tuple[str | None, ...],
    ) -> None:
        """Mark the annotations re-emitted as slot labels as already placed.

        Within a signature an annotation comment *may* be a binding label
        held on the AST and re-emitted by :meth:`_fmt_signature`.
        Retiring those here — rather than letting a claim point skip them
        — means no later claim, including the declaration backstop, can
        print one a second time; the idempotence test catches a
        regression.

        Only the ones actually consumed, though.  The label walk takes the
        first annotation *after* each slot, so a leading annotation, or a
        second one behind an already-labelled slot, belongs to no slot and
        must survive as an ordinary comment.  Matching runs in source
        order against the consumed labels, which the walk produces in slot
        order — the same order.  Pairing is by text, first match wins, so
        it is exact unless an *unconsumed* in-paren annotation shares its
        text with a label consumed by a later slot: then the wrong object
        is retired and the survivors emit out of source order.  Nothing is
        lost and the result is stable; matching by position rather than
        text would remove the caveat.
        """
        wanted = [text for text in consumed if text]
        if not wanted:
            return
        for comment in self._attached.inline:
            if not wanted:
                return
            if (comment.kind == "annotation"
                    and comment.paren_depth > 0
                    and start <= comment.line <= end
                    and comment.text[2:-2].strip() == wanted[0]):
                self._claimed_inline.add(id(comment))
                wanted.pop(0)

    def _claim_inline_range(
        self,
        start: int,
        end: int,
        upper: tuple[int, int] | None = None,
    ) -> None:
        """Claim unplaced inline comments on source lines ``start..end``.

        ``upper`` bounds the claim by a following construct's start
        position.  Two statements can share a line, and a line-granular
        claim would hand both their trailing comments to whichever is
        emitted first, so the cut has to compare full (line, column).
        """
        if not self._lines:
            return
        claimed = [
            c for c in self._attached.inline
            if id(c) not in self._claimed_inline and start <= c.line <= end
            and (upper is None or (c.line, c.column) < upper)
        ]
        if not claimed:
            return
        self._claimed_inline.update(id(c) for c in claimed)
        # A `--` runs to end of line, so anything appended after one is
        # swallowed into its text and stops being a separate comment on
        # re-read.  At most one line comment may share a physical line and
        # it has to be last; whatever follows goes on its own line.  The
        # alternative — sorting line comments last — would reorder them
        # against the source.
        # A `--` runs to end of line, so anything appended after one is
        # swallowed into its text and stops being a separate comment on
        # re-read.  Line comments therefore go last, and everything stays
        # on this one physical line.
        #
        # Spilling the remainder onto a *new* line instead would turn an
        # inline comment into an own-line one, and own-line comments
        # attach to the nearest anchor *after* them — for a comment
        # following the last statement in a block that is the next
        # top-level declaration, so it walks out of the function on each
        # pass.  Reordering within a single claim is the lesser evil: all
        # of these are already being relocated to the same construct, so
        # their relative order carries nothing a reader can rely on.
        blocks = [c for c in claimed if c.kind != "line"]
        lines = [c for c in claimed if c.kind == "line"]
        rendered = [_flatten_comment(c) for c in blocks]
        # Only the final line comment can stay in `--` form; any earlier
        # one is re-delimited as `{- ... -}` so it remains a *distinct*
        # comment on re-read instead of being absorbed into the next.
        for i, comment in enumerate(lines):
            text = _flatten_comment(comment)
            if i == len(lines) - 1 or "-}" in text:
                rendered.append(text)
            else:
                rendered.insert(
                    len(rendered) - 0, "{- " + text[2:].strip() + " -}",
                )
        self._lines[-1] = f"{self._lines[-1]}  {' '.join(rendered)}"

    def _flush_orphan_comments(self, limit: int | None) -> None:
        """Emit every unconsumed `before` bucket keyed below *limit*.

        A bucket no emitter pops is a deleted comment — the mechanism
        behind every silent deletion this formatter has had.  Flushing
        stranded buckets at each declaration boundary makes deletion
        impossible by construction: the worst remaining failure is the
        relocation spec 1.8 rule 11 explicitly sanctions ("the comment
        moves to the end of the enclosing declaration rather than
        being dropped").  ``None`` flushes everything left.
        """
        stranded = sorted(
            key for key in self._attached.before
            if limit is None or key < limit
        )
        for key in stranded:
            for c in self._attached.before.pop(key):
                for cline in c.text.split("\n"):
                    self._line(cline.strip())

    def _drain_comments(self, node: object) -> None:
        """Emit every comment bucketed at or inside *node*'s span.

        For a construct that renders on a single line, the anchors
        inside it exist (attachment needs them) but no emitter visits
        them.  Draining here — before the construct's own line — keeps
        such a comment on the construct it documents rather than
        leaving the bucket for the backstop, one declaration away.
        """
        lines: list[int] = []
        span = getattr(node, "span", None)
        if span:
            lines.append(span.line)
        _collect_interior_anchors(node, lines)
        for anchor in sorted(set(lines)):
            self._emit_comments(anchor)

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
            # `_attach_comments` files a comment above the module line into
            # `before[module_line]`; without this read it is another bucket
            # written and never consumed, and `examples/vera/math.vera`
            # loses its two header lines.
            if prog.module.span:
                self._emit_comments(prog.module.span.line)
            self._emit_module(prog.module)
            self._claim_inline(prog.module)

        if prog.imports:
            if prog.module:
                self._blank()
            for imp in prog.imports:
                if imp.span:
                    self._emit_comments(imp.span.line)
                self._emit_import(imp)
                self._claim_inline(imp)

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
                # Structural backstop, half one: any `before` bucket
                # still keyed below this declaration belonged to an
                # earlier one and can never be consumed now — every
                # remaining anchor is on a later line.  Rule 11 names
                # the fallback: the comment moves to the end of the
                # enclosing declaration rather than being dropped.
                # After this flush, deleting a comment requires
                # deleting it from the attachment map itself; no
                # emitter omission can do it.
                self._flush_orphan_comments(tld.span.line)
                self._emit_comments(tld.span.line)
            self._emit_top_level(tld)
            # Backstop for every declaration form.  `_emit_fn_decl` has its
            # own, but `data`/`type`/`effect`/`ability` have no interior
            # claim points, so without this a trailing comment anywhere in
            # them is filed into `_Attached.inline` and never read — the
            # deletion #1123 fixed for functions only.
            self._claim_inline(tld)

        # Structural backstop, half two: whatever survived the last
        # declaration is emitted here, ahead of the footer.
        self._flush_orphan_comments(None)
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
        parts.append(fn.name + self._fmt_signature(
            fn.params,
            fn.return_type,
            fn.param_annotations,
            fn.return_annotation,
        ))

        self._line(" ".join(parts))
        if fn.span is not None:
            sig_end = (
                fn.return_type.span.end_line
                if fn.return_type.span is not None
                else fn.span.line
            )
            self._suppress_signature_labels(
                fn.span.line,
                sig_end,
                (*(fn.param_annotations or ()), fn.return_annotation),
            )
            self._claim_inline_range(fn.span.line, sig_end)

        # Contract clauses — each on its own line, indented 2 spaces
        self._indent_inc()
        for i, c in enumerate(fn.contracts):
            # Rule 13 applies to any repeated own-line item, not just
            # statements: a gap between two clauses is the same authored
            # paragraph break, and the AST records it nowhere.
            if i:
                self._blank_if_separated(c)
            if c.span:
                self._emit_comments(c.span.line)
            self._emit_contract(c)
            self._claim_inline(c)

        # Effects clause
        self._blank_if_separated(fn.effect)
        if fn.effect.span:
            self._emit_comments(fn.effect.span.line)
        self._line(f"effects({self._fmt_effect_row(fn.effect)})")
        self._claim_inline(fn.effect)
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
            if fn.where_span:
                self._emit_comments(fn.where_span.line)
            self._emit_where_block(fn.where_fns)

        # Backstop: anything inside this declaration that no inner
        # construct claimed (an effects-clause trailer, say) lands here
        # rather than being dropped.  Relocating a comment is recoverable;
        # deleting one is not.
        if fn.span is not None:
            self._claim_inline_range(fn.span.line, fn.span.end_line)

    def _emit_where_block(self, fns: tuple[FnDecl, ...]) -> None:
        self._line("where {")
        for i, fn in enumerate(fns):
            if i > 0:
                self._blank()
            self._indent_inc()
            if fn.span:
                self._emit_comments(fn.span.line)
            self._emit_fn_decl(fn, None)
            self._indent_dec()
        self._line("}")

    def _fmt_signature(
        self,
        params: tuple[TypeExpr, ...],
        return_type: TypeExpr,
        param_annotations: tuple[str | None, ...] | None = None,
        return_annotation: str | None = None,
    ) -> str:
        """Format function signature: (@T1, @T2 -> @R).

        Annotation-comment labels are emitted from the AST, not from the
        extracted comment stream: spec 1.3 makes them part of the AST,
        and each belongs to a slot index rather than to a source line —
        two labels routinely share the signature's line, which the
        line-keyed store this replaced could not represent (#1123).
        """
        # `strict=True` rather than index arithmetic: a desynced
        # `param_annotations` would otherwise silently drop trailing labels
        # (too short) or ghost ones (too long), which is precisely the
        # quiet deletion spec 1.8 rule 11 forbids.  `dataclasses.replace`
        # is the house idiom for rewriting an `FnDecl`, so the arity holds
        # today only because no pass rewrites `params`.
        labels = (
            param_annotations if param_annotations is not None
            else (None,) * len(params)
        )
        param_strs = ", ".join(
            self._fmt_param_type(p) + _annotation_suffix(label)
            for p, label in zip(params, labels, strict=True)
        )
        ret = self._fmt_param_type(return_type) + _annotation_suffix(
            return_annotation,
        )
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
            if ctor.span:
                self._emit_comments(ctor.span.line)
            comma = "," if i < len(data.constructors) - 1 else ""
            if ctor.fields is not None:
                fields = ", ".join(self._fmt_type_bare(f) for f in ctor.fields)
                self._line(f"{ctor.name}({fields}){comma}")
            else:
                self._line(f"{ctor.name}{comma}")
            self._claim_inline(ctor)
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
            if op.span:
                self._emit_comments(op.span.line)
            self._emit_op_decl(op)
            self._claim_inline(op)
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
            if op.span:
                self._emit_comments(op.span.line)
            self._emit_op_decl(op)
            self._claim_inline(op)
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
        """Emit the interior of a block (statements then expression).

        The result expression takes the same gap treatment as a
        statement: it is the last thing in the block, and the break
        before it -- `match ...;`, blank, `()` -- is the commonest
        paragraph break there is.  A walk over `statements` alone leaves
        it stripped.

        Neither the first statement nor a block whose whole content is
        the result expression takes one, though: a gap held against the
        opening brace separates nothing, and rule 2 already gives the
        brace its own line.
        """
        following: list[object] = [*block.statements[1:], block.expr]
        for i, (stmt, nxt) in enumerate(zip(block.statements, following)):
            if i:
                self._blank_if_separated(stmt)
            if stmt.span:
                self._emit_comments(stmt.span.line)
            self._emit_stmt(stmt)
            nxt_span = getattr(nxt, "span", None)
            self._claim_inline(
                stmt,
                (nxt_span.line, nxt_span.column) if nxt_span else None,
            )
        if block.statements:
            self._blank_if_separated(block.expr)
        if block.expr.span:
            self._emit_comments(block.expr.span.line)
        self._emit_block_expr(block.expr)
        self._claim_inline(block.expr)

    def _emit_block_expr(self, expr: Expr) -> None:
        """Emit a block's result expression (may be multi-line)."""
        node = _unwrap_redundant_block(expr)
        if node is not expr and node.span:
            # The same unwrap `_emit_value` and the arm path perform:
            # `{ match ... }` at result position rendered with its
            # redundant wrapper while every other position unwrapped —
            # one construct, two canonical renderings selected by
            # where it sat.  Same comment rescue, same reason.
            self._emit_comments(node.span.line)
        if isinstance(node, IfExpr):
            self._emit_if(node)
        elif isinstance(node, MatchExpr):
            self._emit_match(node)
        elif isinstance(node, HandleExpr):
            self._emit_handle(node)
        elif isinstance(node, Block):
            # Nested block
            self._line("{")
            self._indent_inc()
            self._emit_block_body(node)
            self._indent_dec()
            self._line("}")
        else:
            self._line(self._fmt_expr(node))

    # -- Statements ----------------------------------------------------

    def _emit_stmt(self, stmt: Stmt) -> None:
        # Every statement kind ends in an expression under a `;`, and
        # rule 2 does not care which one introduced it — only the text
        # before the construct differs.  Splitting that text out as a
        # prefix is what lets all three share one rule-2 path.
        if isinstance(stmt, LetStmt):
            te = self._fmt_param_type(stmt.type_expr)
            self._emit_value(stmt.value, f"let {te} = ", ";")
        elif isinstance(stmt, LetDestruct):
            bindings = ", ".join(
                self._fmt_param_type(b) for b in stmt.type_bindings
            )
            self._emit_value(
                stmt.value, f"let {stmt.constructor}<{bindings}> = ", ";",
            )
        elif isinstance(stmt, ExprStmt):
            self._emit_value(stmt.expr, "", ";")

    def _emit_value(self, value: Expr, prefix: str, suffix: str) -> None:
        """Emit an expression in value position, honouring rule 2.

        Rule 2 is unconditional (spec §1.8): a `match`/`if`/`handle`
        opens its brace on the line that introduces it and closes on a
        line of its own, whether it is a statement, a block result, a
        match-arm body, or the value a `let` binds.  Value position
        alone used to flatten, which gave one construct two textual
        forms selected by where it sat — exactly the "equivalent
        alternatives" DESIGN.md principle 3 exists to rule out, and a
        per-site condition a generator would have to evaluate rather
        than the single unconditional rule principle 6 asks for.

        The unwrap is what makes that reachable through a written
        `{ match ... }`: a block holding no statements keeps its
        content in `expr`, so without it `_needs_own_lines` sees a
        Block, answers no, and the construct flattens anyway.
        """
        node = value
        while isinstance(node, Block) and not node.statements:
            # A statement-less wrapper is redundant; the bare content
            # is canonical.  Unwrapping drops the block's span, and
            # any comment anchored at the content's line would go with
            # it — a *discarded* comment, which rule 11 forbids
            # outright.  Emit each level's bucket before it vanishes.
            if node.expr.span:
                self._emit_comments(node.expr.span.line)
            node = node.expr
        if _needs_own_lines(node):
            # The construct's own span line is an anchor, and a value
            # bound directly — no wrapper — still files a comment
            # written between `let ... =` and a next-line construct
            # under it.  Flush unconditionally, not only on unwrap;
            # the guarded form silently deleted that comment.
            if node.span:
                self._emit_comments(node.span.line)
            self._emit_own_lines(node, prefix, suffix)
        elif isinstance(node, Block):
            # A block WITH statements is not redundant — its braces
            # are a scope boundary.  Emit it faithfully in rule-2
            # shape: flattening it emitted `let @T = let @T = ...;`,
            # output that no longer parsed, and deleted any comment
            # anchored on its interior lines.
            self._line(f"{prefix}{{")
            self._indent_inc()
            self._emit_block_body(node)
            self._indent_dec()
            self._line(f"}}{suffix}")
        else:
            self._line(f"{prefix}{self._fmt_expr(node)}{suffix}")

    # -- Multi-line expressions ----------------------------------------

    def _emit_own_lines(
        self, node: Expr, prefix: str = "", suffix: str = "",
    ) -> None:
        """Emit a rule-2 construct, opening on the caller's line.

        The prefix (`Ok(_) -> `) shares the line with the opening
        brace; the closing brace still gets a line of its own.
        """
        if isinstance(node, MatchExpr):
            self._emit_match(node, prefix, suffix)
        elif isinstance(node, IfExpr):
            self._emit_if(node, prefix, suffix)
        elif isinstance(node, HandleExpr):
            self._emit_handle(node, prefix, suffix)
        else:  # pragma: no cover - guarded by _needs_own_lines
            raise AssertionError(f"not a multi-line construct: {node!r}")

    def _emit_if(
        self, expr: IfExpr, prefix: str = "", suffix: str = "",
    ) -> None:
        cond = self._fmt_expr(expr.condition)
        self._line(f"{prefix}if {cond} then {{")
        self._indent_inc()
        self._emit_block_body(expr.then_branch)
        self._indent_dec()
        self._line("} else {")
        self._indent_inc()
        self._emit_block_body(expr.else_branch)
        self._indent_dec()
        self._line(f"}}{suffix}")

    def _emit_match(
        self, expr: MatchExpr, prefix: str = "", suffix: str = "",
    ) -> None:
        scrut = self._fmt_expr(expr.scrutinee)
        self._line(f"{prefix}match {scrut} {{")
        self._indent_inc()
        for i, arm in enumerate(expr.arms):
            comma = "," if i < len(expr.arms) - 1 else ""
            if i:
                self._blank_if_separated(arm)
            if arm.span:
                self._emit_comments(arm.span.line)
            pat = self._fmt_pattern(arm.pattern)
            # A block wrapping nothing but a nested match/if/handle
            # keeps that construct in `expr`, not `statements`, so the
            # test below read it as empty and flattened the whole thing
            # onto one line against rule 2.  Unwrapping drops each
            # wrapper's span, and any comment anchored at its content
            # line would go with it — a *discarded* comment, which
            # rule 11 forbids outright — so every level's bucket is
            # emitted before the unwrap bites, whatever the content.
            body_node = arm.body
            while isinstance(body_node, Block) and not body_node.statements:
                if body_node.expr.span:
                    self._emit_comments(body_node.expr.span.line)
                body_node = body_node.expr
            if isinstance(body_node, Block) and body_node.statements:
                # Multi-statement block: emit multi-line with braces.
                # No span pop here — a braced block's span starts at
                # its first *statement* (Lark meta covers children,
                # not the `{`), and `_emit_block_body` is the
                # comment-aware owner of that anchor; popping it now
                # would pull the statement's comment out of the block.
                self._line(f"{pat} -> {{")
                self._indent_inc()
                self._emit_block_body(body_node)
                self._indent_dec()
                self._line(f"}}{comma}")
            elif _needs_own_lines(body_node):
                # The construct's own line is its anchor; a comment
                # between `->` and a next-line construct files there.
                if body_node.span:
                    self._emit_comments(body_node.span.line)
                self._emit_own_lines(body_node, f"{pat} -> ", comma)
            else:
                # The body's own start line is an anchor: a comment
                # between `->` and a next-line body files under it,
                # and without this pop it drifted to the next arm —
                # or, for the last arm, out of the function to the
                # file footer.
                if body_node.span:
                    self._emit_comments(body_node.span.line)
                body = self._fmt_expr(body_node)
                self._line(f"{pat} -> {body}{comma}")
            # An arm is not a Block, so `_emit_block_body`'s hook never
            # reaches it and every arm comment fell through to the
            # declaration backstop — which piled them all onto the match's
            # closing brace, out of the arm they document.
            nxt = expr.arms[i + 1] if i + 1 < len(expr.arms) else None
            nxt_span = getattr(nxt, "span", None)
            self._claim_inline(
                arm,
                (nxt_span.line, nxt_span.column) if nxt_span else None,
            )
        self._indent_dec()
        self._line(f"}}{suffix}")

    def _emit_handle(
        self, expr: HandleExpr, prefix: str = "", suffix: str = "",
    ) -> None:
        eff = self._fmt_effect_ref(expr.effect)
        state_str = self._fmt_handler_state(expr)
        self._line(f"{prefix}handle[{eff}]{state_str} {{")
        self._indent_inc()
        for i, clause in enumerate(expr.clauses):
            comma = "," if i < len(expr.clauses) - 1 else ""
            if i:
                self._blank_if_separated(clause)
            if clause.span:
                self._emit_comments(clause.span.line)
            # A clause body renders on one line, so every anchor
            # inside it is a position emission never visits.  Drain
            # those buckets here, above the clause they document,
            # rather than let the comment migrate to the next clause
            # or into the `in` block (#1136's misattribution class).
            self._drain_comments(clause.body)
            self._emit_handler_clause(clause, comma)
            nxt = expr.clauses[i + 1] if i + 1 < len(expr.clauses) else None
            nxt_span = getattr(nxt, "span", None)
            self._claim_inline(
                clause,
                (nxt_span.line, nxt_span.column) if nxt_span else None,
            )
        self._indent_dec()
        self._line("} in {")
        self._indent_inc()
        self._emit_block_body(expr.body)
        self._indent_dec()
        self._line(f"}}{suffix}")

    def _fmt_handler_clause(self, clause: HandlerClause) -> str:
        """One clause as a single line, without its separator.

        Shared by the multi-line emitter and the inline renderer: two
        independent renderings of the same node are how the inline path
        came to emit a literal ellipsis while the multi-line one was
        correct.
        """
        params = ", ".join(
            self._fmt_param_type(p) for p in clause.params
        )
        # The wrapper below supplies the clause's braces, so a Block
        # body renders braceless through `_fmt_block_inline`; routing
        # it through `_fmt_expr` would add a second, nested pair.
        #
        # The SECOND site that is not structure-preserving in canonical
        # mode (#1238 round 2), and one the review's own battery missed —
        # found by reading every normalisation site rather than by probing.
        # A bare clause body parses (`put(@Int) -> resume(())`), so
        # `clause.body` is a `Block` for the braced spelling and a plain
        # expression for the bare one; supplying braces unconditionally
        # renders both as `-> { resume(()) }`.  In structural mode the
        # braces follow the AST instead: present exactly when the body is
        # a block, which is what re-parses to the shape it came from.
        body = (
            self._fmt_block_inline(clause.body)
            if isinstance(clause.body, Block)
            else self._fmt_expr(clause.body)
        )
        if self._structural and not isinstance(clause.body, Block):
            rendered_body = body
        else:
            rendered_body = f"{{ {body} }}"

        with_str = ""
        if clause.state_update:
            te = self._fmt_param_type(clause.state_update[0])
            val = self._fmt_expr(clause.state_update[1])
            with_str = f" with {te} = {val}"

        return f"{clause.op_name}({params}) -> {rendered_body}{with_str}"

    def _fmt_handler_state(self, expr: HandleExpr) -> str:
        """The `(@T = init)` initialiser, or nothing at all."""
        if not expr.state:
            return ""
        te = self._fmt_param_type(expr.state.type_expr)
        init = self._fmt_expr(expr.state.init_expr)
        return f"({te} = {init})"

    def _emit_handler_clause(self, clause: HandlerClause, comma: str) -> None:
        self._line(f"{self._fmt_handler_clause(clause)}{comma}")

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
            if (not isinstance(expr.collection, _POSTFIX_SAFE)
                    or self._shows_pipe(expr.collection)):
                # Parenthesization is dropped by the parser, so it must
                # be re-derived here exactly as `_fmt_binary` does for
                # operator children (see _POSTFIX_SAFE).
                coll = f"({coll})"
            idx = self._fmt_expr(expr.index)
            return f"{coll}[{idx}]"

        # Calls
        if isinstance(expr, _CALL_FORMS) and self._shows_pipe(expr):
            return self._fmt_pipe(expr)
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
            # A block reached through a true sub-expression position —
            # an operand, an argument, an element, a condition — keeps
            # its braces: they are grouping and scope.  `{ 1 + 2 } * 3`
            # is 9, and without the braces it reparses as 7; a
            # statement-bearing block loses its scope boundary and its
            # binding leaks into the enclosing block, shifting slot
            # resolution.  Positions where the braces are genuinely
            # redundant (a whole value, an arm body) unwrap at their
            # own emit sites, never here.
            return f"{{ {self._fmt_block_inline(expr)} }}"

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
        """Format a float literal canonically.

        ``repr`` is the shortest round-tripping spelling, but for
        |x| < 1e-4 or >= 1e16 Python switches to exponent notation,
        which FLOAT_LIT (``/[0-9]+\\.[0-9]+/``) cannot lex — the
        formatted program stopped parsing.  Expanding through
        ``Decimal(repr(value))`` is exact: it denotes precisely the
        value repr's digits do, so the positional rendering parses
        back to the identical float.
        """
        s = repr(value)
        if "e" in s or "E" in s:
            s = format(Decimal(s), "f")
        # A whole-valued expansion (`1e+16` -> `10000000000000000`)
        # has no decimal point, which FLOAT_LIT requires.
        if "." not in s and "inf" not in s and "nan" not in s:
            s = s + ".0"
        return s

    def _fmt_binary(self, expr: BinaryExpr) -> str:
        left = self._fmt_expr(expr.left)
        right = self._fmt_expr(expr.right)

        pipes = not self._structural
        if _needs_parens(expr.left, expr.op, "left", pipes=pipes):
            left = f"({left})"
        if _needs_parens(expr.right, expr.op, "right", pipes=pipes):
            right = f"({right})"

        return f"{left} {expr.op.value} {right}"

    def _shows_pipe(self, expr: Expr) -> bool:
        """Whether *expr* prints as a pipe: a piped call, outside STRUCTURAL
        mode.  The spelling flag takes no part in node equality, so the two
        spellings of one call are one predicate to the checker, and the
        structural rendering, which names a State cell after its type
        (:func:`vera.types.structural_type_key`), must not tell them apart
        either: it prints the call."""
        return not self._structural and _is_pipe(expr)

    def _fmt_pipe(
        self, expr: FnCall | ConstructorCall | QualifiedCall | ModuleCall,
    ) -> str:
        """A piped call: its first argument, `|>`, and the call written
        without it.  The left operand never needs parentheses — every other
        operator binds tighter, and a pipe on the left is the chain's own
        left associativity — so it prints as it stands."""
        left = self._fmt_expr(expr.args[0])
        rest = ", ".join(self._fmt_expr(a) for a in expr.args[1:])
        if isinstance(expr, QualifiedCall):
            callee = f"{expr.qualifier}.{expr.name}"
        elif isinstance(expr, ModuleCall):
            callee = f"{'.'.join(expr.path)}::{expr.name}"
        else:
            callee = expr.name
        return f"{left} |> {callee}({rest})"

    def _fmt_unary(self, expr: UnaryExpr) -> str:
        operand = self._fmt_expr(expr.operand)

        # Need parens if operand is binary or is a unary neg (avoid --)
        needs = False
        if (isinstance(expr.operand, BinaryExpr)
                or self._shows_pipe(expr.operand)):
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
        """Format a match arm body, wrapping multi-statement blocks in braces.

        NOT structure-preserving in canonical mode, which is the point of
        the structural flag (#1238 round 2).  `Red -> { e }` parses to
        `Block(expr=e)` and `Red -> e` to `e`; the unwrap below renders both
        as `e`, so the two — which the checker holds apart, `RefinedType`
        equality being dataclass equality over the predicate — name one
        cell family.  In structural mode the wrapper is kept, which
        re-parses to the block it came from, so the left-inverse argument
        that makes this renderer a discriminator survives.
        """
        if isinstance(body, Block):
            if body.statements or self._structural:
                return f"{{ {self._fmt_block_inline(body)} }}"
            # A statement-less wrapper is redundant in arm position;
            # the bare body is canonical, matching the multi-line arm
            # path's unwrap.
            return self._fmt_arm_body(body.expr)
        return self._fmt_expr(body)

    def _fmt_handle_inline(self, expr: HandleExpr) -> str:
        """A `handle` reached through a sub-expression position.

        This returned `handle[E] { ... }` — a literal ellipsis — on the
        belief the path was unreachable, which its `# pragma: no cover`
        recorded.  `handle_expr` is a bare alternative of `primary_expr`
        in the grammar, so it is reachable from every operand, argument
        and element position, and the stub deleted the state
        initialiser, every clause and the `in` body, emitting something
        that no longer parsed.

        The braces here share a line, which rule 2 would not choose.
        That is deliberate and narrow: unparseable output is strictly
        worse than badly-shaped output, because a misformatted program
        can still be reformatted and a destroyed one cannot.  Giving
        nested constructs a multi-line path so this renderer is never
        needed is the wider fix.
        """
        eff = self._fmt_effect_ref(expr.effect)
        state = self._fmt_handler_state(expr)
        clauses = ", ".join(
            self._fmt_handler_clause(c) for c in expr.clauses
        )
        body = self._fmt_block_inline(expr.body)
        return f"handle[{eff}]{state} {{ {clauses} }} in {{ {body} }}"

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

class FormatterPostconditionError(RuntimeError):
    """The formatter produced output that violates its own contract.

    Raised instead of returning the output: canonical text corrupted
    by ``vera fmt --write`` is unrecoverable source damage, so a
    violated invariant must be loud, never silent.
    """


def _comment_content(text: str) -> str:
    """A comment's content, delimiters and whitespace normalised.

    Conservation is asserted on content rather than raw text because
    the formatter may legitimately re-delimit a comment (a non-final
    inline ``--`` becomes ``{- -}`` so it survives re-reading) and
    collapses interior whitespace when flattening a multi-line one.
    """
    if text.startswith("--"):
        body = text[2:]
    elif text.startswith("{-") and text.endswith("-}"):
        body = text[2:-2]
    elif text.startswith("/*") and text.endswith("*/"):
        body = text[2:-2]
    else:  # pragma: no cover - scan_comments yields no other shape
        body = text
    return " ".join(body.split())


def _format_once(source: str, file: str | None = None) -> str:
    """One pass of the formatter, without the postcondition check."""
    comments = extract_comments(source)
    tree = vera_parse(source, file=file)
    program = transform(tree)
    attached = _attach_comments(comments, program)
    fmt = Formatter(attached, blank_source_lines(source))
    return fmt.format_program(program)


def _check_postconditions(
    source: str,
    output: str,
    file: str | None,
) -> None:
    """Verify the formatter's three output invariants, loudly.

    DESIGN.md principle 5 — contracts as the source of truth — applies
    to the toolchain itself: the formatter's postconditions are checked
    on every run rather than assumed.  The three invariants:

    1. the output re-parses (a formatter must never destroy a program);
    2. every comment is conserved, by content multiset (spec 1.8
       rule 11 — relocation is sanctioned, deletion never);
    3. the output is a fixed point (canonical form is canonical).

    Violation raises :class:`FormatterPostconditionError` naming the
    broken invariant, so corrupt output is never returned — and never
    written by ``vera fmt --write``, which only sees the exception.
    """
    label = file if file is not None else "<source>"
    tail = "This is a formatter bug; the input file was not modified."
    try:
        second = _format_once(output)
    except Exception as exc:  # converted, not swallowed — re-raised below
        raise FormatterPostconditionError(
            f"formatter postcondition violated for {label}: the "
            f"formatted output does not re-parse ({exc}).  {tail}"
        ) from exc
    src_comments = Counter(
        _comment_content(c.text) for c in extract_comments(source)
    )
    out_comments = Counter(
        _comment_content(c.text) for c in extract_comments(output)
    )
    if src_comments != out_comments:
        lost = sorted((src_comments - out_comments).elements())
        gained = sorted((out_comments - src_comments).elements())
        raise FormatterPostconditionError(
            f"formatter postcondition violated for {label}: comment "
            f"conservation failed (spec 1.8 rule 11).  "
            f"Lost: {lost!r}; duplicated or invented: {gained!r}.  "
            f"{tail}"
        )
    if second != output:
        raise FormatterPostconditionError(
            f"formatter postcondition violated for {label}: the output "
            f"is not a fixed point — a second pass would rewrite it, "
            f"so it is not canonical form.  {tail}"
        )


def format_expr_canonical(expr: Expr, *, structural: bool = False) -> str:
    """One expression, in canonical single-line source form.

    *structural* renders for DISCRIMINATION instead: identical output
    except at the two sites where canonical form CHOOSES between AST
    shapes the checker holds apart — a match arm's redundant block wrapper
    and a handler clause's braces (see :meth:`Formatter._fmt_arm_body` and
    :meth:`Formatter._fmt_handler_clause`) — and at a piped call, which the
    checker does NOT hold apart from the call written out, and which
    structural mode therefore prints as that call
    (:meth:`Formatter._shows_pipe`).  Both spellings stay re-parseable, so
    the left-inverse argument below holds in either mode; only in
    structural mode does it also hold *between* those two shapes.
    :func:`vera.types.structural_type_key` passes ``structural=True``,
    because there the rendering NAMES a State cell and two predicates
    rendering alike is two cells sharing one.  ``vera fmt`` does not, so
    canonical output is untouched.

    The expression half of :func:`format_source`, reached without a source
    buffer: the same :meth:`Formatter._fmt_expr` that formats a contract
    clause or a `let` value, over an empty comment attachment (an expression
    rendered in isolation has no comments to place, and none of them are
    part of the expression anyway).

    **A left inverse of parsing, which is what makes it usable as a
    discriminator** (#1218 / PR #1238 review).  Parenthesisation is not
    copied from the source — the parser discards it — but RE-DERIVED from
    precedence and associativity by :func:`_needs_parens`, precisely so the
    output re-parses to the expression it came from.  So ``parse(format(e))
    == e``, and therefore ``format(a) == format(b)`` implies ``a == b``:
    ``(a + b) + c`` renders ``a + b + c`` while ``a + (b + c)`` keeps its
    parentheses, and the two never collide.  ``vera fmt``'s idempotence
    postcondition and ``scripts/check_corpus_canonical.py`` exercise that
    round trip over the whole corpus on every commit, so the property is a
    maintained gate rather than an argument.

    :func:`vera.types.structural_type_key` uses this to render a refinement
    predicate, which is what keeps a refined cell's family name LINEAR in
    the predicate's source length.  ``ast.Node.pretty`` — the obvious
    alternative, and what the key used first — is a newline-indented tree
    whose size grows quadratically in nesting depth: 44 left-nested ``&&``
    conjuncts render 56,604 characters there against 646 here, and mangled
    that crossed the WASM name-section limit.
    """
    return Formatter(
        _Attached(before={}, inline=[], header=[], footer=[]),
        structural=structural,
    )._fmt_expr(expr)


def format_source(source: str, file: str | None = None) -> str:
    """Format Vera source code to canonical form.

    Parses *source*, formats the AST, re-inserts comments, and returns
    the canonically-formatted string.  *file* is a diagnostic label
    only; the text formatted is always *source*.

    Every call checks the formatter's postconditions (see
    :func:`_check_postconditions`) and raises
    :class:`FormatterPostconditionError` rather than returning output
    that fails them.

    Raises ``VeraError`` on parse failure.
    """
    output = _format_once(source, file=file)
    _check_postconditions(source, output, file)
    return output
