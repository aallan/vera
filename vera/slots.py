"""Slot resolution tables, and the two walks that are not about naming.

:func:`slot_table` computes a function's slot resolution table from its
parameter type expressions and a module's :class:`~vera.naming.AliasEnv` —
what ``vera check --explain-slots`` prints, and what the verifier and the
LSP map a ``@T.n`` back to a parameter with.  The naming itself is
:mod:`vera.naming`'s (#1208): the table reports the names the checker
actually bound and every consumer resolves against, so it cannot tell the
user something no subsystem agrees with.

What remains here is deliberately NOT naming.
:func:`type_expr_slot_name` is the alias-opaque syntactic spelling the WASM
representation walks want, and :func:`family_fallback_name` is what a
State/Exn cell family falls back on when its type expression names no
family at all.  Each says why in its own docstring.  The family itself
renders through :func:`vera.naming.family_name` (#1209).

The De Bruijn convention: @T.0 is the *last* (rightmost) parameter of
type T in the signature; @T.1 is second-to-last; and so on.  For a
function ``fn foo(@Int, @Int -> @Int)``:
  - @Int.0 → parameter 2 (last @Int)
  - @Int.1 → parameter 1 (first @Int)
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Container, Iterable, Iterator

from vera import ast, naming
from vera.naming import AliasEnv

__all__ = [
    "bare_call_denotes_user_fn",
    "effect_op_result_names",
    "family_fallback_name",
    "fn_scopes",
    "fn_slot_scope",
    "format_slot_table",
    "slot_table",
    "slot_table_dict",
    "type_expr_slot_name",
]


# ------------------------------------------------------------------
# Bare-call ownership: whose declaration does this name denote?
# ------------------------------------------------------------------

def bare_call_denotes_user_fn(
    name: str, user_fn_names: Container[str],
) -> bool:
    """Whether a BARE call to *name* denotes a USER function (#1284).

    THE one answer to "is this ``get`` the user's declaration or the
    handler's operation?", for every subsystem that has to know.  The rule
    is the type checker's, because the checker's answer is the one the
    program was accepted under: :meth:`CallsMixin._check_call_with_args`
    looks a bare name up as a *function* before it looks it up as an effect
    operation, so a declaration named ``get`` owns every bare ``get(...)``
    in its scope — provably, since an arity or argument-type error at such
    a call site reports against the USER's signature (E201/E202), never the
    operation's.  Spec §7.4 resolves a bare op only for a name no
    declaration occupies.

    Consumers, each passing its OWN name table:

    * the checker's ``_check_call_with_args`` — the derivation, over its
      LEXICAL function scope (#991);
    * the checker's ``_collect_expr_effects``, the ``async(e)``
      commutativity walk, so the row it reasons about is the row the
      resolution above bound;
    * ``_translate_call`` in :mod:`vera.wasm.calls` — the bare dispatch, over
      codegen's ``_scoped_fns`` (``_fn_sigs`` narrowed to the compiling
      declaration's lexical scope, #1299): a user-owned name skips the
      clause-inline registry, the host-cell intrinsics, and the #1233
      addressability gate, and lowers as the ordinary call it is;
    * the three bare-``FnCall`` inference sites in :mod:`vera.wasm.inference`
      and :mod:`vera.wasm.context`, so a shadowed name is typed from the
      function table rather than from the operation's result registry;
    * ``_handle_exn_always_throws`` in :mod:`vera.wasm.calls_handlers`, whose
      ``throw_installed`` question is the same one for ``Exn``'s operation:
      a bare ``throw`` in a clause body is the op only where no declaration
      owns the name;
    * :class:`~vera.monomorphize.Monomorphizer`'s discovery walk, over
      ``MonoContext.fn_names``, so the clone it discovers for a ``get(())``
      in a value position is the clone the rewrite emits.  That table is
      program-wide rather than per-scope, so a name it must not claim is
      kept OUT of it instead: a qualified-only module generic contributes
      no bare ``_fn_sigs`` entry at all (#1281).

    What this deliberately does NOT gate is the op REGISTRIES themselves.
    "Whose name is this?" and "which cell does the operation reach?" are two
    questions, and answering the second with the first is what #1284 was:
    the registries stay complete, so the QUALIFIED spelling
    (``State.get(())``, which names the effect and so cannot be shadowed),
    ``new(State<T>)``, ``old(State<T>)``, and the addressability gate keep
    reaching their cell in a program that also declares ``fn get``.

    *user_fn_names* is a membership view, not a fixed set, so each consumer
    supplies the table it actually resolves against.  One rule over two
    tables is one answer only where both tables are SCOPES, and codegen's
    was not: it passed a flat mirror of every symbol the whole compilation
    absorbed, which keys a name the call site cannot SEE under its bare
    name, so this predicate answered "user-owned" where the checker had
    resolved the operation (#1299).  Codegen now passes ``_scoped_fns`` —
    ``_fn_sigs`` narrowed to the compiling declaration's lexical scope by
    ``CodeGenerator._scoped_fn_names`` — while the flat registry stays
    behind ``_known_fns`` for the guard rail, which asks the different and
    genuinely flat question "does this resolved target have a symbol?".

    Four routes reached that divergence, and the narrowing closes them
    together because they were one defect: an imported module's ``private
    fn get``, a public one a selective import excludes, a ``where`` helper
    of a ``forall<T>`` parent, and — through the INTRINSIC gate rather than
    the op one — the ability operation ``show``, which E151 does not
    reserve.  The ``where``-helper route is the one worth spelling out,
    because the other three make it tempting to think module scope is
    enough.  Under a NON-generic parent a helper is safe: #1015 and the
    non-generic hoist move it out of the bare namespace before registration
    (a local one is ``holder$where$get``) and rewrite its holder's call
    sites with it, so it shadows the name in its own body and nowhere else.
    Under a GENERIC parent it keeps a bare ``_fn_sigs`` key beside its
    clone-qualified one (measured: ``helper`` and ``id`` in
    ``tests/conformance/ch09_generic_where_helper.vera``) — and it IS in
    the module, so only the LEXICAL rule excludes it from a sibling's
    scope while leaving it in its own parent's.
    """
    return name in user_fn_names


# ------------------------------------------------------------------
# Canonical slot-name construction (single source of truth)
# ------------------------------------------------------------------

def type_expr_slot_name(te: ast.TypeExpr) -> str | None:
    """The SYNTACTIC full-depth type name of a TypeExpr, or ``None``.

    NOT a slot-environment key and NOT a slot-reference lookup: both of
    those render through :mod:`vera.naming` against a module's alias
    environment (#1208), because a name minted one way and looked up
    another misses silently.  What remains here is the alias-OPAQUE
    spelling — no environment, so nothing to resolve against — which is
    what the two REPRESENTATION walks want: the hop-by-hop alias
    canonicalization behind the WASM width / erasure deciders
    (``_canonicalize_alias_slot_name``) and the structural-``Eq``
    derivability oracle (``_ground_field_type_name``).  Both ask a
    question about a type's machine representation, one alias hop at a
    time; neither keys a binding.

    A parameterized type recurses into its type arguments to a
    FULLY-QUALIFIED name, so nested composites stay distinguishable
    (``Option<Tuple<Int, Int>>`` and ``Option<Tuple<Bool, Bool>>`` do NOT
    collapse to one ``Option<Tuple>`` — the pre-#914 one-level bug).
    Refinements resolve to their base name only.

    Returns ``None`` when a component is neither a `NamedType` nor a
    `RefinementType` chain over one — e.g. a `FnType` **nested inside** a
    type argument.  A top-level `FnType` yields the synthetic ``"Fn"``.
    """
    if isinstance(te, ast.NamedType):
        if te.type_args:
            inner_names: list[str] = []
            for a in te.type_args:
                inner = type_expr_slot_name(a)
                if inner is None:
                    return None
                inner_names.append(inner)
            return f"{te.name}<{', '.join(inner_names)}>"
        return te.name
    if isinstance(te, ast.RefinementType):
        return type_expr_slot_name(te.base_type)
    if isinstance(te, ast.FnType):
        return "Fn"
    return None


def effect_op_result_names(
    effects: Iterable[ast.EffectRefNode],
) -> dict[str, str]:
    """Effect-op name → the Vera type name a call to it RESULTS in (#1207).

    THE one table behind the ``_effect_op_result_vera`` mirror (#1006).
    Three consumers read an operation's result type to name a clone, and
    they must land on one name or the clone discovery emits dangles at the
    call the rewrite emits (a loud E602 skip, and the caller drops with
    E620):

    * ``codegen/functions.py`` builds the per-function registry from the
      declared ``effects(<State<T>>)`` row;
    * ``CallsHandlersMixin._translate_handle_state`` replaces it for the
      duration of a ``handle[State<T>]`` body; and
    * :class:`~vera.monomorphize.Monomorphizer`'s discovery walk consults
      it for a ``get(())`` in a value position — which, before this
      existed, fell through to the literal-driven ``Int`` default while
      the rewrite read the cell's ``Nat``.

    ``State<T>`` yields ``{"get": <T>}``; ``put`` produces ``Unit`` and
    ``Exn<E>``'s ``throw`` diverges, so neither records a result type
    (absent, matching codegen's ``None``).  The name is the alias-OPAQUE
    source spelling from :func:`type_expr_slot_name` — ``State<Count>``
    with ``type Count = Nat`` names the clone ``pick$Count``, not
    ``pick$Nat`` — because that is what the WASM rewrite records and a
    resolution applied on one side only would dangle exactly as before.

    SOURCE ORDER, first wins, and an effect whose type argument has no
    slot name at all contributes nothing: both mirror the guards in
    ``codegen/functions.py``'s row loop, which a divergence here would
    desync from.  Shadowing is NOT filtered here and no caller filters it
    on the way in (#1284): this table says what the operation results in,
    and whether a given call site is the operation at all is
    :func:`bare_call_denotes_user_fn`'s question, asked at the call site.
    """
    out: dict[str, str] = {}
    for eff in effects:
        if not isinstance(eff, ast.EffectRef):
            continue
        if eff.name != "State" or not eff.type_args:
            continue
        if len(eff.type_args) != 1:
            continue
        name = type_expr_slot_name(eff.type_args[0])
        if name is not None:
            out.setdefault("get", name)
    return out


# ------------------------------------------------------------------
# Internal helpers
# ------------------------------------------------------------------

def _te_slot_name(te: ast.TypeExpr, env: AliasEnv) -> str:
    """Return the slot-matching name for a parameter TypeExpr (#1208).

    :func:`vera.naming.slot_name` against the module's naming environment —
    the ONE renderer, so the table reports the names the checker actually
    bound and every consumer resolves against, not a syntactic rebuild of
    them.  Already ``str``-total: an unresolvable component is ``"?"``.
    """
    return naming.slot_name(te, env)


def fn_slot_scope(
    env: AliasEnv, forall_vars: Iterable[str] | None,
) -> AliasEnv:
    """*env* as seen from INSIDE a function with those type parameters.

    A ``forall<T>`` variable shadows a same-named module alias for the whole
    signature — the checker binds it in ``_check_fn`` step 1, before it
    renders any parameter or reference — so both sides of a slot lookup have
    to be rendered here, never against the bare module environment.  One
    helper rather than a ``with_type_params`` call per consumer, so the
    binding side (:func:`slot_table`) and the reference side
    (:func:`vera.naming.slot_ref_key`) cannot end up scoped differently.
    """
    return naming.with_type_params(env, forall_vars) if forall_vars else env


def fn_scopes(
    decl: ast.FnDecl,
    inherited: Iterable[str] = (),
    _path: tuple[str, ...] = (),
) -> Iterator[tuple[ast.FnDecl, tuple[str, ...], tuple[str, ...]]]:
    """*decl* and every function nested in its ``where`` block, in source
    order, as ``(fn, type parameters in scope OVER it, qualified name path)``.

    A ``where`` helper sees its parent's ``forall`` variables as well as its
    own: ``_check_fn`` saves and restores one shared type-parameter map
    rather than replacing it, so entering a helper ADDS to the scope.  The
    accumulated tuple is therefore what :func:`fn_slot_scope` has to be given
    for a helper — narrowed by the parent's variables, a same-named module
    alias stays shadowed all the way down, and rendering the helper against
    the bare module environment silently merges parameter stacks the checker
    keeps apart.

    The path is the enclosing function names followed by this one, so its
    length carries the nesting depth and its join is a name unique within the
    module (helpers of two different functions may share a bare name).

    One walk rather than one per consumer (``vera check --explain-slots`` and
    the LSP's go-to-definition, #1217): both ask the same question about the
    same nesting, and an accumulation that differed between them would put
    the two surfaces' answers about one helper out of step.
    """
    in_scope = (*inherited, *(decl.forall_vars or ()))
    path = (*_path, decl.name)
    yield decl, in_scope, path
    for helper in decl.where_fns or ():
        yield from fn_scopes(helper, in_scope, path)


def _label(tname: str, slot_idx: int, n: int) -> str:
    """Human-readable label for a slot entry, e.g. 'last @Int'."""
    if n == 1:
        return f"only @{tname}"
    if slot_idx == 0:
        return f"last @{tname}"
    if slot_idx == n - 1:
        return f"first @{tname}"
    return f"{n - slot_idx} from last @{tname}"


# ------------------------------------------------------------------
# Public API
# ------------------------------------------------------------------

def slot_table(
    params: tuple[ast.TypeExpr, ...],
    env: AliasEnv,
    forall_vars: Iterable[str] | None,
) -> dict[str, list[int]]:
    """Return the slot resolution table for a function's parameter list.

    Returns ``{type_name: [1-based param positions, slot-0-first]}``.

    Example: ``(@Int, @Int)`` → ``{"Int": [2, 1]}``
    meaning ``@Int.0`` = parameter 2, ``@Int.1`` = parameter 1.

    *env* is the module's naming environment (#1208): the table is a NAMING
    answer, so it is rendered by the one renderer rather than rebuilt
    syntactically.  Required rather than defaulted — an empty environment
    silently renders every alias opaquely, which is the failure mode the
    consolidation exists to close.

    *forall_vars* is the owning function's own type parameters (``None`` for
    a non-generic one), which SHADOW same-named module aliases for the whole
    signature — the checker binds its parameters with them already in scope
    (``_check_fn`` step 1, before step 4's slot binding), so a table rendered
    without them can disagree.  Concretely, under ``type T = Int`` the
    signature ``forall<T> fn g(@Option<Int>, @Option<T>)`` binds two stacks
    for the checker and ONE for a module-only rendering — which then reports
    ``@Option<Int>.0`` as parameter 2 where the checker resolves it to
    parameter 1.  Required, not defaulted, for the same reason *env* is: the
    omission has no symptom of its own.
    """
    scope = fn_slot_scope(env, forall_vars)
    by_type: dict[str, list[int]] = defaultdict(list)
    for i, te in enumerate(params, 1):
        by_type[_te_slot_name(te, scope)].append(i)
    return {tname: list(reversed(pos)) for tname, pos in by_type.items()}


def substitute_parameters(
    expr: ast.Expr,
    params: tuple[ast.TypeExpr, ...],
    args: tuple[ast.Expr, ...],
    env: AliasEnv,
    forall_vars: Iterable[str] | None,
) -> ast.Expr | None:
    """*expr*, written over *params*, with each parameter slot replaced by
    the argument *args* passes in that position.

    A callee's precondition rendered at a call site: `requires(@Int.0 <
    string_length(@String.0))` at `string_char_code("abc", @Nat.0)` becomes
    `@Nat.0 < string_length("abc")`.  The slot table is the one
    :func:`slot_table` builds, so a reference resolves to the parameter the
    checker bound it to.  Returns ``None`` when a reference cannot be mapped
    — a type the table does not hold, an index past its stack, an argument
    list too short — rather than a partial substitution, which would leave a
    parameter slot to be resolved against the CALLER's scope.
    """
    import dataclasses

    table = slot_table(params, env, forall_vars)
    scope = fn_slot_scope(env, forall_vars)

    class _Unmapped(Exception):
        pass

    def rebuild(node: ast.Expr) -> ast.Expr:
        if isinstance(node, ast.SlotRef):
            positions = table.get(naming.slot_ref_key(node, scope))
            if not positions or node.index >= len(positions):
                raise _Unmapped
            pos = positions[node.index]
            if pos > len(args):
                raise _Unmapped
            return args[pos - 1]
        changes: dict[str, object] = {}
        for f in dataclasses.fields(node):
            value = getattr(node, f.name)
            if isinstance(value, ast.Expr):
                new_value = rebuild(value)
                if new_value is not value:
                    changes[f.name] = new_value
            elif (isinstance(value, tuple) and value
                    and all(isinstance(x, ast.Expr) for x in value)):
                new_tuple = tuple(rebuild(x) for x in value)
                if any(a is not b for a, b in zip(new_tuple, value)):
                    changes[f.name] = new_tuple
        if changes:
            # dataclasses.replace's typeshed overload cannot see the
            # per-subclass field types through **dict.
            return dataclasses.replace(node, **changes)  # type: ignore[arg-type]
        return node

    try:
        return rebuild(expr)
    except _Unmapped:
        return None


def format_slot_table(
    fn_name: str,
    params_str: str,
    table: dict[str, list[int]],
    depth: int = 0,
) -> str:
    """Format a human-readable slot environment block for one function.

    Returns a multi-line string suitable for printing to stdout.  EVERY line
    carries a leading indent — at ``depth=0`` the ``fn`` line is indented two
    spaces and its slot rows four, two more of each per ``where`` level — so
    the block below is what the caller prints, shifted right by two::

        fn divide(@Int, @Int -> @Int)
          @Int.0  parameter 2 (last @Int)
          @Int.1  parameter 1 (first @Int)

    *depth* is the ``where``-nesting level (#1217): a helper is indented one
    step further than its parent and labelled ``where fn``, so the printed
    tables carry the nesting that decides which parameters a ``@T.n`` inside
    the helper can name.
    """
    indent = "  " * (depth + 1)
    keyword = "where fn" if depth else "fn"
    lines = [f"{indent}{keyword} {fn_name}({params_str})"]
    for tname in sorted(table):
        positions = table[tname]
        n = len(positions)
        for slot_idx, param_pos in enumerate(positions):
            lines.append(
                f"{indent}  @{tname}.{slot_idx}  "
                f"parameter {param_pos} ({_label(tname, slot_idx, n)})"
            )
    return "\n".join(lines)


def slot_table_dict(
    fn_name: str,
    table: dict[str, list[int]],
) -> dict[str, object]:
    """Return a JSON-serialisable slot table for a single function.

    *fn_name* is the function's qualified name — ``parent.helper`` for a
    ``where``-block helper (#1217) — because a helper may share its bare name
    with a helper of another function, and a consumer keying on ``function``
    would silently collapse the two.
    """
    entries: list[dict[str, object]] = []
    for tname in sorted(table):
        for slot_idx, param_pos in enumerate(table[tname]):
            entries.append({
                "slot": f"@{tname}.{slot_idx}",
                "type": tname,
                "parameter": param_pos,
            })
    return {"function": fn_name, "slots": entries}


def family_fallback_name(te: ast.TypeExpr) -> str:
    """The last-resort name for a ``State<T>`` / ``Exn<E>`` cell FAMILY.

    The family itself resolves — :func:`vera.naming.family_name` names the
    CELL the checker typed, so every spelling that resolves to one cell
    mangles to one import and one tag (#1209), including one whose
    resolution carries a function type (#1219) or a refinement predicate
    (#1218).  What is left for here is the residue that resolution cannot
    name: a type expression whose resolution is a BARE function type or
    ``UnknownType`` (an ``FnType``-bodied alias as ``State<F>``, an
    arity-mismatched alias application, a removed alias).  Those have no
    cell type to name, so the family falls back on the alias-OPAQUE
    syntactic spelling — distinct per spelling, which is the conservative
    direction: it can only ever split a family the checker already refuses
    to type, never merge two the checker keeps apart.

    Total, because a family must always have a name to mangle.  Derived here
    rather than passed in by each call site: the fallback and the resolution
    are one decision about one type expression, and the four methods that
    make it — ``WasmContext._family_name`` / ``._family_base`` and
    ``CodeGenerator._family_name_te`` / ``._family_base_te``, the identity
    and representation halves on each side — are the only places allowed to
    make it.  All four fall back on the SAME type expressions, so a consumer
    can never hold an identity for a cell whose representation it cannot
    name, or the reverse.
    """
    return type_expr_slot_name(te) or "?"
