"""Check-time SQL literal-provenance resolution (#309).

The ``<DB>`` effect (#229) runs ``query`` / ``execute`` against a host database.
The soundness layer #309 makes SQL injection a **compile-time** error: the SQL
(first) argument of a built-in ``DB`` SQL op must be *literal-provenance* — a
value assembled entirely from string literals, never from a runtime slot, a
function result, or a ``\\(expr)`` interpolation of a runtime value.  A
non-literal SQL string is the injection vector, so the checker rejects it
outright (E207) — deterministic, solver-free, and effective even inside handled
code where Z3-based claims cannot reach.

:func:`resolve_literal_string` is the core: it returns the compile-time value of
a ``String`` expression **iff** that value is provably literal, else ``None``.
The default for any expression shape it does not explicitly assemble is
``None`` — *conservative reject*.  That asymmetry is the soundness guarantee: a
missing or unhandled case can only false-**reject** a valid program (annoying,
never unsafe), never wrong-**accept** a runtime-derived string (an injection).
``WALKER_COVERAGE`` (#597) forces every future ``Expr`` subclass to be given a
disposition here rather than silently defaulting.

The mechanism is *eager*: a ``let`` binding records its resolved literal (if
any) as ``Binding.literal_str`` at the moment it is checked (before ``bind()``),
so a slot referenced later reads a value resolved in *its own* scope — the
De Bruijn-safe way to follow a ``let`` chain without re-walking a shifted
environment.  :func:`resolve_literal_string` therefore only has to read the
stored ``literal_str`` when it reaches a :class:`~vera.ast.SlotRef`.

:func:`count_placeholders` counts positional ``?`` placeholders quote-aware
(a ``?`` inside a SQL string literal is data, not a placeholder), the count the
E208 arity check compares against a statically-sized params array.  Its verdict
MUST agree with what the sqlite3 host binds; that lockstep is pinned by the
differential ``tests/test_sql_provenance_309.py`` against sqlite3 itself.
"""
from __future__ import annotations

from vera import ast

# ``TypeEnv`` is imported lazily inside the function signature via TYPE_CHECKING
# to avoid a runtime import cycle (environment -> checker -> sql -> environment).
from collections.abc import Callable
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera.environment import TypeEnv

# How to render a ``SlotRef`` into the key its binding was stored under.
# Passed in rather than imported, because the CHECKER's renderer is the only
# correct one here: ``TypeEnv.bind`` is keyed via ``_type_expr_to_slot_name``,
# which RESOLVES type arguments, so ``@Array<Option<Txt>>`` with
# ``type Txt = String`` is stored as ``Array<Option<String>>``.  The syntactic
# renderer in :mod:`vera.slots` returns the surface form and would miss — and a
# miss reads as "not statically known", i.e. silence.  Callers pass
# ``ResolutionMixin._slot_ref_key``.
SlotKey = Callable[[ast.SlotRef], str]


def resolve_literal_string(expr: ast.Expr, env: TypeEnv,
                           slot_key: SlotKey) -> str | None:
    """Return the compile-time value of ``expr`` iff it is literal-provenance.

    Returns the resolved ``str`` for a string literal, an interpolation whose
    every embedded expression itself resolves, a ``string_concat`` of two
    resolving operands, or a slot whose binding carries a ``literal_str``.
    Returns ``None`` for anything else — the conservative reject that keeps the
    gate sound: ``None`` means "not provably literal", so the caller rejects.

    # WALKER_COVERAGE: (#597 — every Expr subclass has a disposition; a new
    # subclass added to vera/ast.py trips check_walker_coverage.py until it is
    # given one here.  The default disposition is None = "not literal
    # provenance", which is always SOUND: it can only false-reject.)
    #
    #   StringLit          → Handled: the literal value.
    #   InterpolatedString → Handled: join fragments + recursively-resolved
    #                        embedded exprs; any non-resolving embed → None
    #                        (a runtime \\(expr) is the injection vector).
    #   FnCall             → Handled: string_concat(a, b) of two resolving
    #                        operands; every other builtin/user call → None.
    #   SlotRef            → Handled: the binding's eager literal_str (or None).
    #   BinaryExpr         → None: arithmetic/comparison/logic operators don't
    #                        yield String.  (A `|>` pipe is the FnCall it
    #                        stands for, resolved by the FnCall arm.)
    #   UnaryExpr          → None: no String-producing unary operator exists.
    #   IndexExpr          → None: an indexed element is a runtime value.
    #   IntLit             → None: not a String.
    #   FloatLit           → None: not a String.
    #   BoolLit            → None: not a String.
    #   UnitLit            → None: not a String.
    #   HoleExpr           → None: a typed hole DOES reach here (the resolvers
#                        run during typechecking, not after) — reject.
    #   ResultRef          → None: @T.result is a runtime value.
    #   ConstructorCall    → None: a constructor value is not a bare String.
    #   NullaryConstructor → None: likewise (None / a nullary ctor).
    #   QualifiedCall      → None: a module-qualified call is a runtime result.
    #   ModuleCall         → None: a module call is a runtime result.
    #   AnonFn             → None: a closure is not a String.
    #   IfExpr             → None: conservative — even two literal arms reject
    #                        in v1 (safe; extendable later).
    #   MatchExpr          → None: conservative, as IfExpr.
    #   Block              → None: conservative — a block result is not walked.
    #   HandleExpr         → None: a handled expression is a runtime result.
    #   OldExpr            → None: contract-only; cannot occur in op-arg pos.
    #   NewExpr            → None: contract-only.
    #   AssertExpr         → None: yields Unit; not a String source.
    #   AssumeExpr         → None: yields Unit.
    #   ForallExpr         → None: Bool, contract-only.
    #   ExistsExpr         → None: Bool, contract-only.
    #   ArrayLit           → None: an array is not a String.
    """
    if isinstance(expr, ast.StringLit):
        return expr.value

    if isinstance(expr, ast.InterpolatedString):
        out: list[str] = []
        for part in expr.parts:
            if isinstance(part, str):
                out.append(part)
                continue
            sub = resolve_literal_string(part, env, slot_key)
            if sub is None:
                return None
            out.append(sub)
        return "".join(out)

    if isinstance(expr, ast.FnCall):
        if expr.name == "string_concat" and len(expr.args) == 2:
            left = resolve_literal_string(expr.args[0], env, slot_key)
            right = resolve_literal_string(expr.args[1], env, slot_key)
            if left is None or right is None:
                return None
            return left + right
        return None

    if isinstance(expr, ast.SlotRef):
        binding = env.resolve_slot_binding(slot_key(expr), expr.index)
        return binding.literal_str if binding is not None else None

    # Every other Expr subclass: not literal-provenance (see WALKER_COVERAGE).
    return None


def resolve_array_len(expr: ast.Expr, env: TypeEnv,
                      slot_key: SlotKey) -> int | None:
    """Return ``expr``'s compile-time length iff it is a literal array (#1160).

    The array-side counterpart of :func:`resolve_literal_string`, used by the
    E208 arity check.  Returns the element count for an array literal written
    inline, or for a slot whose binding carries an eager ``array_len`` — so a
    params array moved into a ``let`` for readability is checked exactly as the
    inline form is.  Returns ``None`` for anything else, which defers the count
    to the sqlite3 host at run time.

    ``None`` is the conservative answer in the *opposite* direction from
    :func:`resolve_literal_string`.  There, ``None`` means "reject": a
    non-resolving SQL string is the injection vector.  Here ``None`` means
    "don't check": E208 is a completeness diagnostic, not a soundness one — a
    real mismatch still fails at run time as ``Result.Err``.  So a missed shape
    costs a compile-time error that could have been raised, never a wrongly
    rejected program.  Do not "fix" a miss by guessing a length.

    Deliberately narrower than the string resolver: it does *not* fold
    ``array_concat`` or any other builtin.  Each extra shape folded here is
    another way to compute a WRONG length and false-reject a valid program —
    the one outcome this check must never produce.  ``test_array_concat_defers``
    and ``test_unequal_if_arms_defer`` pin that.

    # WALKER_COVERAGE: (#597 — every Expr subclass has a disposition; a new
    # subclass added to vera/ast.py trips check_walker_coverage.py until it is
    # given one here.  The default disposition is None = "length not statically
    # known", which can only UNDER-report: a missed shape costs an E208 that
    # could have been raised, never a wrongly rejected program.)
    #
    #   ArrayLit           → Handled: the element count.
    #   SlotRef            → Handled: the binding's eager array_len (or None).
    #   FnCall             → None: a builtin/user call result has no static
    #                        length.  Deliberately NOT folding array_concat &
    #                        co — see the note above on wrong lengths.
    #   QualifiedCall      → None: an effect-op result is a runtime value.
    #   ModuleCall         → None: likewise, across a module boundary.
    #   IndexExpr          → None: an indexed element, not the array itself.
    #   IfExpr             → None: conservative — even two same-length arms
    #                        defer in v1 (safe; extendable later).
    #   MatchExpr          → None: conservative, as IfExpr.
    #   Block              → None: conservative — a block result is not walked.
    #   HandleExpr         → None: a handled expression is a runtime result.
    #   BinaryExpr         → None: no operator yields an Array (a `|>` pipe is
    #                        the FnCall it stands for).
    #   UnaryExpr          → None: no Array-producing unary operator exists.
    #   ConstructorCall    → None: an ADT value, not a bare Array.
    #   NullaryConstructor → None: likewise.
    #   AnonFn             → None: a closure is not an Array.
    #   StringLit          → None: not an Array.
    #   InterpolatedString → None: not an Array.
    #   IntLit             → None: not an Array.
    #   FloatLit           → None: not an Array.
    #   BoolLit            → None: not an Array.
    #   UnitLit            → None: not an Array.
    #   HoleExpr           → None: a typed hole DOES reach here (the resolvers
#                        run during typechecking, not after) — defer.
    #   ResultRef          → None: @T.result is a runtime value.
    #   OldExpr            → None: contract-only; cannot occur in op-arg pos.
    #   NewExpr            → None: contract-only.
    #   AssertExpr         → None: yields Unit.
    #   AssumeExpr         → None: yields Unit.
    #   ForallExpr         → None: Bool, contract-only.
    #   ExistsExpr         → None: Bool, contract-only.
    """
    if isinstance(expr, ast.ArrayLit):
        return len(expr.elements)

    if isinstance(expr, ast.SlotRef):
        binding = env.resolve_slot_binding(slot_key(expr), expr.index)
        return binding.array_len if binding is not None else None

    return None


def _is_sqlite_id_char(ch: str) -> bool:
    """True if ``ch`` is a SQLite identifier / bind-parameter-name character.

    SQLite's ``IdChar`` accepts alphanumerics, ``_``, ``$``, and ANY byte
    ``>= 0x80`` (every byte of a non-ASCII UTF-8 character), so a ``:name`` /
    ``@name`` / ``$name`` bind parameter whose first name character is non-ASCII
    or ``$`` — ``:€x``, ``:£x``, ``$$x``, ``@¥v`` — is a NAMED parameter to the
    sqlite3 host.  Python ``str.isalnum()`` is ``False`` for high-byte SYMBOL
    characters (``£``, ``€``) and for ``$``, so using it alone under-detected
    these: ``count_placeholders`` returned a positional ``int`` instead of
    ``None``, the gate emitted no ``E209`` (or a wrong ``E208``), and a query the
    host binds by name passed ``check`` then failed at run time (#1147
    adversarial workflow).  This mirrors sqlite3 so the count defers on exactly
    what the host binds by name.
    """
    return ch.isalnum() or ch == "_" or ch == "$" or ord(ch) >= 0x80


def count_placeholders(sql: str) -> int | None:
    """Count anonymous ``?`` placeholders in ``sql``, quote- and comment-aware.

    Returns the number of anonymous ``?`` placeholders — what the sqlite3 host
    binds a *positional* params array against — so it is the count the E208
    arity check compares to a statically-sized params array.  A ``?`` inside a
    string literal (``'...'`` / ``"..."``), a quoted identifier (``` `...` ```
    backtick / ``[...]`` bracket), or a ``--`` line / ``/* ... */`` block comment
    is data, not a placeholder, and is skipped (SQL's doubled-delimiter escape
    inside a ``'`` / ``"`` / ``` ` ``` string is handled; ``[...]`` has no escape,
    a ``]`` always closes).

    Returns ``None`` when the SQL uses a NON-anonymous placeholder syntax —
    numbered (``?NNN``) or named (``:name`` / ``@name`` / ``$name``) — because
    the plain positional count no longer equals the number of bound parameters
    (``?1 ... ?1`` binds one; ``:a AND :b`` binds two with zero ``?``).  There
    is no arity to check in that case, and the caller does not try: Vera's
    params API is positional-only, so :mod:`vera.checker.calls` rejects the SQL
    outright with E209 rather than reaching the E208 comparison.  ``None`` is
    therefore "not countable", not "allowed through" — no such program reaches
    run time.  The ``?``-only agreement with sqlite3 is pinned by the
    differential in ``tests/test_sql_provenance_309.py``.
    """
    count = 0
    quote: str | None = None      # active string/identifier delimiter, else None
    i = 0
    n = len(sql)
    while i < n:
        c = sql[i]
        if quote is not None:
            if c == quote:
                # A doubled delimiter ('', "", ``) is an escaped delimiter,
                # still inside the string/identifier — skip both characters.
                # ([...] bracket quoting has no escape: a ] always closes.)
                if quote != "]" and i + 1 < n and sql[i + 1] == quote:
                    i += 2
                    continue
                quote = None
            i += 1
            continue
        # Outside a quote, skip SQL comments whole so their contents
        # (apostrophes, ? marks) affect neither quote tracking nor the count —
        # sqlite3 ignores them too.
        if c == "-" and i + 1 < n and sql[i + 1] == "-":
            nl = sql.find("\n", i + 2)          # line comment: to end of line
            i = n if nl == -1 else nl + 1
            continue
        if c == "/" and i + 1 < n and sql[i + 1] == "*":
            end = sql.find("*/", i + 2)         # block comment: to closing */
            i = n if end == -1 else end + 2
            continue
        if c in ("'", '"', "`"):
            quote = c                           # string / backtick identifier
        elif c == "[":
            quote = "]"                         # bracket identifier, closed by ]
        elif c == "?":
            # ?NNN is a NUMBERED placeholder — the positional count is unreliable
            # (a repeated ?N binds once), so defer the arity check to the host.
            if i + 1 < n and sql[i + 1].isdigit():
                return None
            count += 1
        elif c in (":", "@", "$") and i + 1 < n and _is_sqlite_id_char(
            sql[i + 1]
        ) and not (
            # ``$`` is a valid mid-token identifier char in SQLite — ``a$b`` is
            # ONE identifier, not a ``$name`` param — so it begins a named
            # placeholder only at a token boundary, never right after an
            # identifier char.  ``:`` and ``@`` cannot appear inside an
            # identifier, so they always begin a param.
            c == "$" and i > 0 and _is_sqlite_id_char(sql[i - 1])
        ):
            # :name / @name / $name is a NAMED placeholder — likewise defer.
            return None
        i += 1
    return count
