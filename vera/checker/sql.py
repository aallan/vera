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
Each resolver is a ``vera.fold.dispatch`` table, which forces every future
``Expr`` subclass to be given an arm here rather than silently defaulting.

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

from vera import ast, fold

# ``TypeEnv`` is imported lazily inside the function signature via TYPE_CHECKING
# to avoid a runtime import cycle (environment -> checker -> sql -> environment).
from collections.abc import Callable, Mapping
from typing import TYPE_CHECKING, Any

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
    Each class's answer is its arm in ``_LITERAL_STRING_ARMS``.
    """
    arm = _LITERAL_STRING_ARMS.get(type(expr))
    return arm(expr, env, slot_key) if arm is not None else None


def _literal_interpolation(expr: ast.InterpolatedString, env: TypeEnv,
                           slot_key: SlotKey) -> str | None:
    # Join the fragments and the recursively-resolved embedded exprs; any
    # non-resolving embed is None (a runtime \(expr) is the injection vector).
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


def _literal_call(expr: ast.FnCall, env: TypeEnv,
                  slot_key: SlotKey) -> str | None:
    # string_concat(a, b) of two resolving operands; every other builtin or
    # user call is a runtime result.
    if expr.name == "string_concat" and len(expr.args) == 2:
        left = resolve_literal_string(expr.args[0], env, slot_key)
        right = resolve_literal_string(expr.args[1], env, slot_key)
        if left is None or right is None:
            return None
        return left + right
    return None


def _literal_slot(expr: ast.SlotRef, env: TypeEnv,
                  slot_key: SlotKey) -> str | None:
    # The binding's eager literal_str (or None).
    binding = env.resolve_slot_binding(slot_key(expr), expr.index)
    return binding.literal_str if binding is not None else None


def _not_literal(expr: ast.Expr, env: TypeEnv,
                 slot_key: SlotKey) -> str | None:
    return None


_LiteralArm = Callable[[Any, "TypeEnv", SlotKey], "str | None"]

#: Each expression class's literal provenance.  Every class but the four
#: that assemble a literal is None, "not literal provenance", which is
#: always SOUND: it can only false-reject.
_LITERAL_STRING_ARMS: Mapping[type[ast.Expr], _LiteralArm] = fold.dispatch(
    "resolve_literal_string", {
        ast.StringLit: lambda expr, env, slot_key: expr.value,
        ast.InterpolatedString: _literal_interpolation,
        ast.FnCall: _literal_call,
        ast.SlotRef: _literal_slot,
        **fold.each((
            # Operators yield no String (a `|>` pipe is the FnCall it stands
            # for), an index or a result reference is a runtime value, and
            # a literal of another type is not a String.
            ast.BinaryExpr, ast.UnaryExpr, ast.IndexExpr, ast.IntLit,
            ast.FloatLit, ast.BoolLit, ast.UnitLit, ast.ResultRef,
            # A typed hole DOES reach here (the resolvers run during
            # typechecking, not after): reject.
            ast.HoleExpr,
            # A constructor value, a qualified or module call's result, a
            # closure, an array: not a bare literal String.
            ast.ConstructorCall, ast.NullaryConstructor, ast.QualifiedCall,
            ast.ModuleCall, ast.AnonFn, ast.ArrayLit,
            # Conservative: even two literal arms reject in v1 (safe;
            # extendable later), and a block or a handled result is not
            # walked.
            ast.IfExpr, ast.MatchExpr, ast.Block, ast.HandleExpr,
            # Contract-only, or Unit / Bool valued.
            ast.OldExpr, ast.NewExpr, ast.AssertExpr, ast.AssumeExpr,
            ast.ForallExpr, ast.ExistsExpr,
        ), _not_literal),
    })


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
    and ``test_unequal_if_arms_defer`` pin that.  Each class's answer is its
    arm in ``_ARRAY_LEN_ARMS``.
    """
    arm = _ARRAY_LEN_ARMS.get(type(expr))
    return arm(expr, env, slot_key) if arm is not None else None


def _array_slot(expr: ast.SlotRef, env: TypeEnv,
                slot_key: SlotKey) -> int | None:
    # The binding's eager array_len (or None).
    binding = env.resolve_slot_binding(slot_key(expr), expr.index)
    return binding.array_len if binding is not None else None


def _length_unknown(expr: ast.Expr, env: TypeEnv,
                    slot_key: SlotKey) -> int | None:
    return None


_LengthArm = Callable[[Any, "TypeEnv", SlotKey], "int | None"]

#: Each expression class's static array length.  Every class but an array
#: literal and a slot is None, "length not statically known", which can only
#: UNDER-report: a missed shape costs an E208 that could have been raised,
#: never a wrongly rejected program.
_ARRAY_LEN_ARMS: Mapping[type[ast.Expr], _LengthArm] = fold.dispatch(
    "resolve_array_len", {
        ast.ArrayLit: lambda expr, env, slot_key: len(expr.elements),
        ast.SlotRef: _array_slot,
        **fold.each((
            # A call's result has no static length: deliberately NOT
            # folding array_concat & co (see the note above on wrong
            # lengths), and an effect-op or module call is a runtime value.
            ast.FnCall, ast.QualifiedCall, ast.ModuleCall,
            # An indexed element, not the array itself.
            ast.IndexExpr,
            # Conservative: even two same-length arms defer in v1 (safe;
            # extendable later), and a block or a handled result is not
            # walked.
            ast.IfExpr, ast.MatchExpr, ast.Block, ast.HandleExpr,
            # No operator yields an Array (a `|>` pipe is the FnCall it
            # stands for), and an ADT, a closure, a String or a scalar is
            # not one.
            ast.BinaryExpr, ast.UnaryExpr, ast.ConstructorCall,
            ast.NullaryConstructor, ast.AnonFn, ast.StringLit,
            ast.InterpolatedString, ast.IntLit, ast.FloatLit, ast.BoolLit,
            ast.UnitLit,
            # A typed hole DOES reach here (the resolvers run during
            # typechecking, not after): defer.
            ast.HoleExpr,
            # A runtime value, contract-only, or Unit / Bool valued.
            ast.ResultRef, ast.OldExpr, ast.NewExpr, ast.AssertExpr,
            ast.AssumeExpr, ast.ForallExpr, ast.ExistsExpr,
        ), _length_unknown),
    })


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
