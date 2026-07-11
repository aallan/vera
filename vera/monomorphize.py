"""Shared generic-function monomorphization: instantiation discovery + AST
substitution.

Extracted from ``vera/codegen/monomorphize.py`` so that BOTH codegen (Pass 1.5,
for WASM emission) and the verifier (#732, per-monomorphization static
verification) drive the SAME discovery + substitution logic.  Sharing one
implementation is a *soundness requirement*: the verifier must check exactly the
instantiation set codegen emits, or a missed instantiation becomes a false
Tier-1 — ``vera verify`` reports clean while a runtime obligation is left
unproven.

This module is deliberately codegen-free.  Its only imports are :mod:`vera.ast`
and the pure :func:`substitute_type_vars` ``TypeExpr`` walk (relocated here from
``vera/wasm/inference.py`` so importing the monomorphizer doesn't pull in the
``vera.wasm`` backend).  WASM/layout-specific concerns — ability-constraint
checking (E613) and layout-derived ``Eq`` auto-derivation — stay in
``vera/codegen/monomorphize.py``.

Discovery + substitution are exposed as methods on :class:`Monomorphizer`, which
holds a :class:`MonoContext` of registration metadata.  Each consumer builds the
context from its own state (codegen from its layout/signature mixin, the
verifier from :class:`~vera.environment.TypeEnv`) and runs its own *orchestration*
(worklist) — codegen filters constraint-failing instances via ``_check_constraints``
while building WAT; the verifier discovers a constraint-agnostic superset.  The
leaf inference + substitution they call is identical, which is what keeps the two
instantiation sets in agreement.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields, replace
from typing import Any

from vera import ast
from vera.slots import slot_ref_name, type_expr_slot_name


def substitute_type_vars(
    te: ast.TypeExpr,
    subst: dict[str, ast.TypeExpr],
) -> ast.TypeExpr:
    """Substitute type variables inside a TypeExpr.

    Module-level so it's accessible from `InferenceMixin`
    (`vera/wasm/inference.py` — the canonicaliser, called from
    interpolation/apply_fn inference), `CodeGenerator`
    (`vera/codegen/core.py` — the compilability check
    `_type_expr_to_wasm_type`), and :func:`resolve_fn_type_alias`
    below — the shared transitive walker behind
    `Monomorphizer._resolve_arg_fn_shape` /
    `CallsMixin._resolve_arg_fn_shape_wasm` (#604 / #659 CR-4 +
    CR-5, routed through the resolver by PR #880).  All sites need
    the same substitution semantics when
    following a parameterised alias (`type Box<T> = Array<T>`,
    `type Mapper<T> = fn(T -> T)`) so the alias's own type-param
    references in the body get bound to the concrete type arguments
    from the call site (#635 closes the compilability-side gap that
    PR #631's walker fix didn't reach).

    A "type variable reference" is a bare `NamedType(name=X,
    type_args=None|())` whose name is a key in `subst`; it gets
    replaced wholesale by `subst[X]`.  `NamedType` with non-bare
    type_args is recursed into (substituting in each arg).
    `RefinementType` substitutes its `base_type`; the `predicate`
    is left untouched (predicates are `Expr`, not `TypeExpr`, and
    canonicalisation is type-level only).  `FnType` substitutes
    through each param and the return type (added by #659 CR-4 +
    CR-5 for parameterised FnType aliases).  Other shapes pass
    through unchanged.
    """
    if isinstance(te, ast.NamedType):
        if not te.type_args and te.name in subst:
            return subst[te.name]
        if te.type_args:
            new_args = tuple(
                substitute_type_vars(a, subst) for a in te.type_args
            )
            return ast.NamedType(name=te.name, type_args=new_args)
        return te
    if isinstance(te, ast.RefinementType):
        new_base = substitute_type_vars(te.base_type, subst)
        return ast.RefinementType(
            base_type=new_base, predicate=te.predicate)
    if isinstance(te, ast.FnType):
        new_params = tuple(
            substitute_type_vars(p, subst) for p in te.params
        )
        new_return = substitute_type_vars(te.return_type, subst)
        # `effect` is passed through unchanged.  All current
        # parameterised FnType aliases use `effects(pure)` or
        # similarly-monomorphic effects.  If a future type
        # introduces `effects(<State<T>>)` or similar where `T`
        # is an alias parameter, the substitution would NOT
        # propagate into the effect row — this is a deliberate
        # gap noted in the #659 review (type-design analyzer
        # finding 3).  The corresponding regression test in
        # `tests/test_wasm.py::TestSubstituteTypeVarsFnType`
        # pins this contract so a future refactor doesn't
        # silently change behaviour.
        return ast.FnType(
            params=new_params,
            return_type=new_return,
            effect=te.effect,
        )
    return te


def resolve_fn_type_alias(
    te: ast.TypeExpr,
    type_aliases: dict[str, ast.TypeExpr],
    type_alias_params: dict[str, tuple[str, ...]],
) -> ast.FnType | None:
    """Resolve a ``TypeExpr`` to the ``FnType`` it aliases, transitively.

    The single transitive-alias-to-fn-type resolver behind every site
    that discovers a function type through an alias — the ``apply_fn``
    ``call_indirect`` signature builder (``_infer_apply_fn_return_type``),
    its Vera-type twin (``_infer_fncall_vera_type``), the fused-await
    classifier (``_apply_fn_closure_ret_type``,
    ``vera/wasm/async_fusion.py``), and the generic higher-order-fn
    consultors (``Monomorphizer._resolve_arg_fn_shape`` /
    ``_infer_fn_alias_type_args`` below, and their WASM call-rewrite
    twins in ``vera/wasm/calls.py``).  Routing every site through this
    one walker makes their depth-N behaviour structurally identical
    rather than replicated per-site: a single-level unwrap at any one
    site desynced it from the signal it must agree with (#867 — a
    two-hop ``type Fetcher = InnerFetcher;`` resolved one hop, saw a
    ``NamedType`` not a ``FnType``, bailed, and consultors diverged
    into a silent identity await / an ``i64``-defaulted
    ``call_indirect`` signature that trapped at WASM validation; the
    PR #880 review found the same single-hop miss in the generic-HOF
    consultors, where a closure-bound type param fell to the
    phantom-var default).

    Lives here — the deliberately codegen-free shared monomorphizer
    module (see the module docstring / #732) — so the WASM backend,
    the codegen-free fusion predicates, and the monomorphizer can all
    import it without an import cycle (``vera/wasm/async_fusion.py``
    imports this module, so it cannot host a helper this module needs).

    Walks iteratively (until the terminal ``FnType``, a non-resolvable
    shape, or a cycle):

    1. Unwraps ``RefinementType`` layers (any nesting depth).
    2. Treats a bared ``FnType`` as terminal wherever it appears —
       including an alias body that is a refinement DIRECTLY wrapping
       an inline fn type (``type Foo = { @fn(...) | p };`` — PR #880
       review, CodeRabbit Major: pre-fix the peeled ``FnType`` fell
       through the ``NamedType`` check to ``None``).
    3. For a ``NamedType`` whose ``type_aliases`` body is a ``FnType``,
       substitutes the current ``NamedType``'s ``type_args`` into the
       alias's type params (for a generic alias like
       ``type Producer<T> = fn(String -> T)``) and loops — the
       substituted ``FnType`` terminates at step 2.
    4. For a ``NamedType`` aliasing another ``NamedType`` /
       ``RefinementType``, substitutes any generic type args at this hop
       and follows the chain one step.
    5. Anything else (a bare ``NamedType`` that is not an alias, a
       primitive) yields ``None`` — no ``FnType`` reachable.

    The ``seen`` set guards against a cyclic alias chain
    (``type A = B; type B = A``).  The type checker rejects circular
    aliases upstream (``[E132]``, #648), so a cycle here can only arise
    from malformed input; the guard makes the resolver terminate with
    ``None`` (the caller then falls to its loud backstop) rather than
    spin forever — the same defence-in-depth
    ``InferenceMixin._resolve_base_type_name`` and
    ``_canonical_named_type`` carry.
    """
    seen: set[str] = set()
    while True:
        while isinstance(te, ast.RefinementType):
            te = te.base_type
        if isinstance(te, ast.FnType):
            return te
        if not isinstance(te, ast.NamedType):
            return None
        if te.name in seen:
            return None
        seen.add(te.name)
        alias = type_aliases.get(te.name)
        if alias is None:
            return None
        # Bind this hop's concrete type args to the alias's params so a
        # generic alias body's type-var references resolve to the bound
        # types (``type Producer<T> = fn(String -> T)`` used as
        # ``Producer<Future<...>>`` → ``fn(String -> Future<...>)``).
        params = type_alias_params.get(te.name)
        if params and te.type_args and len(params) == len(te.type_args):
            alias = substitute_type_vars(alias, dict(zip(params, te.type_args)))
        if isinstance(alias, (ast.FnType, ast.NamedType, ast.RefinementType)):
            te = alias
            continue
        return None


def substitute_type_param_names(name: str, mapping: dict[str, str]) -> str:
    """Substitute type-parameter NAMES inside a type-name *string* (#773).

    ``substitute_type_param_names("List<T>", {"T": "Int"})`` → ``"List<Int>"``.
    A string-level wrapper over :func:`substitute_type_vars`: the name is
    parsed to a :class:`~vera.ast.NamedType`, each bare occurrence of a mapped
    parameter is replaced by the (parsed) concrete argument, and the result is
    re-formatted.  Used by structural-Eq derivation to resolve a declared
    constructor field type like ``List<T>`` or ``Box<T>`` against a concrete
    instantiation's type arguments — the *bare*-param field case (``T``) is
    handled positionally by ``_ctor_adt_tp_indices`` upstream; this covers
    parameters nested inside a parameterized field type (the recursive-ADT
    tail ``Cons(T, List<T>)`` being the canonical case).
    """
    if not mapping or "<" not in name:
        # A bare name is either unmapped or handled positionally upstream;
        # only parameterized field types need the deep walk.
        return mapping.get(name, name)
    parsed = Monomorphizer._parse_type_name(name)
    subst: dict[str, ast.TypeExpr] = {
        param: Monomorphizer._parse_type_name(concrete)
        for param, concrete in mapping.items()
    }
    substituted = substitute_type_vars(parsed, subst)
    if isinstance(substituted, ast.NamedType):
        return Monomorphizer._format_type_name(substituted)
    return name  # pragma: no cover — NamedType in, NamedType out


def declared_return_clone_key(te: ast.TypeExpr | None) -> str | None:
    """The clone-name KEY a user fn's declared return TypeExpr contributes when
    its call result is bound to a generic's type variable.

    THE single source of truth for this key — discovery
    (:func:`vera.codegen.monomorphize._simple_return_type_name`), the #732
    verifier (``ContractVerifier._simple_type_name``), and the WASM call-rewrite
    (``InferenceMixin._declared_return_clone_name``) ALL delegate here, so the
    three consultors cannot desync by construction (#878 / #899 whack-a-mole:
    each independently re-derived this key and they diverged on parameterized
    returns and scalar-resolving aliases, dropping ``main`` at run time on a
    check-green program).

    Convention — refinement-unwrap, then the **base name** with type args
    DROPPED:

      * ``@Decimal``                 → ``"Decimal"``
      * ``@Age`` (``type Age = Int``) → ``"Age"``  (RAW alias, not resolved)
      * ``@Option<Decimal>``          → ``"Option"`` (base name only)
      * ``@{ @Int | p }``             → ``"Int"``  (refinement-unwrapped)
      * a bare ``FnType`` / anything without a NamedType base → ``None``

    The base-name-only key is **sound** for the bare-``@T`` binding it feeds:
    a ``forall<T>`` body binding a whole ADT to ``@T`` (``pick(@T, @T -> @T)``)
    is representation-polymorphic — it can only move/copy the ``i32`` handle,
    never pattern-match or project ``T`` (the body doesn't know ``T``'s
    constructors), so ``Option<Decimal>`` and ``Option<Int>`` share one identity
    clone ``pick$Option`` with byte-identical WAT.  (A parameterized *parameter*
    like ``Option<T>`` — where the body CAN project the field — is a different
    path that recovers the full type argument via ``_get_arg_type_info*``; this
    key is only the bare-``@T`` case.)
    """
    while isinstance(te, ast.RefinementType):
        te = te.base_type
    if isinstance(te, ast.NamedType):
        return te.name
    return None


def mangle_type_name(type_name: str) -> str:
    """Escape a canonical Vera type name for embedding in a WAT identifier.

    The ONE escape convention for type names in WAT symbols (#775): both the
    structural-Eq helper namer (``$eq_<type>``, ``vera/wasm/operators.py``,
    #773) and the mono-clone namer (:meth:`Monomorphizer._mangle_fn_name`)
    delegate here, so the two naming families cannot drift apart.

    Encoding: ``_`` doubles to ``__``; the type-grammar metacharacters get
    distinct ``_X`` codes — ``<`` → ``_L``, ``>`` → ``_R``, ``, ``/``,`` →
    ``_C``, `` `` → ``_S``.

    Injectivity (over canonical type names, as produced by
    :meth:`Monomorphizer._format_type_name`): the output is a concatenation
    of code units, each either a single non-``_`` character (mapping to
    itself) or a two-character code starting with ``_`` (``__``, ``_L``,
    ``_R``, ``_C``, ``_S``).  A left-to-right scan decodes uniquely: at a
    ``_`` consume two characters, otherwise one — a prefix code, so no two
    inputs share an output.  (``A, B`` / ``A,B`` both encode to ``A_CB``,
    but canonical names always spell the separator ``", "``, so only one
    preimage exists in the domain.)  This kills the ``g<Map<String, Int>>``
    vs ``g<Map_String_Int>`` collision class from #775: the former encodes
    its brackets (``Map_LString_CInt_R``) while the flat ADT name doubles
    its underscores (``Map__String__Int``).
    """
    return (
        type_name.replace("_", "__")
        .replace("<", "_L").replace(">", "_R")
        .replace(", ", "_C").replace(",", "_C").replace(" ", "_S")
    )


# Two-char escape code -> the canonical character(s) it decodes to.
# `_C` decodes to the canonical separator spelling `", "` (mangle collapses
# both `", "` and `","` to `_C`, but canonical type names always spell the
# separator `", "`, so that is the sole preimage in the domain).
_UNMANGLE_CODES = {"_": "_", "L": "<", "R": ">", "C": ", ", "S": " "}


def collect_nested_generic_decls(
    decl: ast.FnDecl,
    out: dict[str, ast.FnDecl],
) -> None:
    """Collect ``forall<T>`` where-helpers under an all-NON-generic ancestor
    chain into *out* (#990).

    A generic helper nested in a non-generic function's ``where`` block is a
    monomorphization base exactly like a top-level generic: its concrete call
    sites need clones emitted (codegen Pass 1.5) and verified per
    instantiation (the #732 loop).  This is the SHARED collector both sides
    build their base set with, so they collect the identical set by
    construction — the verifier⊇codegen differential
    (``tests/test_monomorphize_differential.py``) pins the lockstep.

    Stops at the first generic node: a generic helper's own subtree is NOT
    descended (each clone carries it and codegen hoists it per-instantiation,
    #904 — collecting it here would double-emit), and callers only pass
    non-generic roots.  ``setdefault`` keeps first-seen-wins on a bare-name
    collision, matching how plain where-helpers flatten into the bare WASM
    namespace; per-scope duplicate-name semantics are #991's subject.
    """
    for wfn in decl.where_fns or ():
        if wfn.forall_vars:
            out.setdefault(wfn.name, wfn)
        else:
            collect_nested_generic_decls(wfn, out)


def unmangle_type_name(mangled: str) -> str:
    """Inverse of :func:`mangle_type_name` over canonical type names.

    :func:`mangle_type_name` is a prefix code — the output is a concatenation
    of code units, each either a single non-``_`` character (mapping to
    itself) or a two-character ``_X`` code (``__``/``_L``/``_R``/``_C``/``_S``)
    — so a left-to-right scan decodes uniquely: at a ``_`` consume two
    characters and emit the decoded character(s), otherwise consume one and
    emit it.  Round-trips every canonical type name
    (``unmangle_type_name(mangle_type_name(t)) == t``), which is what lets the
    verifier's Array-element reverse lookup (``_get_element_sort_for_array``
    in ``vera/smt.py``) recover the ``_z3_sorts`` key (``List<Int>``) from a
    mangled Array-element sort name (``List_LInt_R``) after #884 routed ADT
    sort names through the mangler.

    Raises ``ValueError`` on a string that is not valid mangler output (a
    trailing lone ``_`` or an unknown ``_X`` code) — such input is outside the
    mangler's range and has no preimage.
    """
    out: list[str] = []
    i = 0
    n = len(mangled)
    while i < n:
        ch = mangled[i]
        if ch != "_":
            out.append(ch)
            i += 1
            continue
        if i + 1 >= n:
            raise ValueError(f"trailing lone '_' in mangled name: {mangled!r}")
        code = mangled[i + 1]
        decoded = _UNMANGLE_CODES.get(code)
        if decoded is None:
            raise ValueError(
                f"unknown escape code '_{code}' in mangled name: {mangled!r}"
            )
        out.append(decoded)
        i += 2
    return "".join(out)


# Sentinel marking a genuinely-FREE (un-inferred) type-parameter slot in a
# partially-recovered sparse-multi-parameter ADT name (`Res<?, Int>`, #898).
# `?` cannot occur in a real Vera type name, so it never collides with a
# concrete type; such a name reaches only the ability gate (the instance is
# always rejected), never an emitted clone, and lets the gate tell an
# under-determined-but-would-derive type (E619, annotate the free param) from
# one whose known component is already non-Eq (E613, annotation cannot help).
_FREE_TYPE_PARAM = "?"


# Builtin function name → SIMPLE Vera return-type name (type args dropped).
# Consulted by Monomorphizer._infer_fncall_vera_type_simple() (instantiation
# discovery) AND by the WASM call-rewrite chain
# (InferenceMixin._infer_fncall_vera_type, vera/wasm/inference.py) — the two
# consultors that must agree on clone names, or discovery emits one mangled
# suffix while the call site references another (dangling E602, #769 gap 1b).
# REGISTRY-COMPLETE (#769): covers every registered builtin whose return has
# a concrete outer constructor (TypeEnv._register_builtins is the key oracle;
# tests/test_codegen_monomorphize.py::TestBuiltinReturnTables769 enforces it).
# Values preserve the rewrite chain's historical names verbatim — e.g.
# string_length is "Int" (the WAT-collapsed name), string_char_code is
# "Nat" — because clone-NAME agreement is the invariant, not name precision;
# changing a value is a clone-granularity decision, not a completion.
# Bare-TypeVar returns (option_unwrap_or, await, …) must stay OUT: a fixed
# entry would bind phantom vars.  Ability-op names (show/hash) and apply_fn
# are not registry builtins and keep their logic arms in the chain.
_BUILTIN_VERA_RETURN_TYPES: dict[str, str] = {
    # array
    "array_all": "Bool",
    "array_any": "Bool",
    "array_append": "Array",
    "array_concat": "Array",
    "array_filter": "Array",
    "array_find": "Option",
    "array_flatten": "Array",
    "array_length": "Int",
    "array_map": "Array",
    "array_mapi": "Array",
    "array_range": "Array",
    "array_reverse": "Array",
    "array_slice": "Array",
    "array_sort_by": "Array",
    # async
    "async": "Future",
    # base64
    "base64_decode": "Result",
    "base64_encode": "String",
    # bool_to
    "bool_to_string": "String",
    # byte_to
    "byte_to_int": "Int",
    "byte_to_string": "String",
    # char
    "char_to_lower": "String",
    "char_to_upper": "String",
    # decimal
    "decimal_abs": "Decimal",
    "decimal_add": "Decimal",
    "decimal_compare": "Ordering",
    "decimal_div": "Option",
    "decimal_eq": "Bool",
    "decimal_from_float": "Decimal",
    "decimal_from_int": "Decimal",
    "decimal_from_string": "Option",
    "decimal_mul": "Decimal",
    "decimal_neg": "Decimal",
    "decimal_round": "Decimal",
    "decimal_sub": "Decimal",
    "decimal_to_float": "Float64",
    "decimal_to_string": "String",
    # float
    "float_clamp": "Float64",
    "float_is_infinite": "Bool",
    "float_is_nan": "Bool",
    "float_to_int": "Int",
    "float_to_string": "String",
    # html
    "html_attr": "Option",
    "html_parse": "Result",
    "html_query": "Array",
    "html_text": "String",
    "html_to_string": "String",
    # int_to
    "int_to_byte": "Option",
    "int_to_float": "Float64",
    "int_to_nat": "Option",
    "int_to_string": "String",
    # is_
    "is_alpha": "Bool",
    "is_alphanumeric": "Bool",
    "is_digit": "Bool",
    "is_lower": "Bool",
    "is_upper": "Bool",
    "is_whitespace": "Bool",
    # json
    "json_array_get": "Option",
    "json_array_length": "Int",
    "json_as_array": "Option",
    "json_as_bool": "Option",
    "json_as_int": "Option",
    "json_as_number": "Option",
    "json_as_object": "Option",
    "json_as_string": "Option",
    "json_get": "Option",
    "json_get_array": "Option",
    "json_get_bool": "Option",
    "json_get_int": "Option",
    "json_get_number": "Option",
    "json_get_string": "Option",
    "json_has_field": "Bool",
    "json_keys": "Array",
    "json_parse": "Result",
    "json_stringify": "String",
    "json_type": "String",
    # map_
    "map_contains": "Bool",
    "map_get": "Option",
    "map_insert": "Map",
    "map_keys": "Array",
    "map_new": "Map",
    "map_remove": "Map",
    "map_size": "Int",
    "map_values": "Array",
    # math/misc
    "abs": "Nat",
    "acos": "Float64",
    "asin": "Float64",
    "atan": "Float64",
    "atan2": "Float64",
    "ceil": "Int",
    "clamp": "Int",
    "cos": "Float64",
    "e": "Float64",
    "floor": "Int",
    "infinity": "Float64",
    "log": "Float64",
    "log10": "Float64",
    "log2": "Float64",
    "max": "Int",
    "min": "Int",
    "nan": "Float64",
    "pi": "Float64",
    "pow": "Float64",
    "round": "Int",
    "sign": "Int",
    "sin": "Float64",
    "sqrt": "Float64",
    "tan": "Float64",
    # md_
    "md_extract_code_blocks": "Array",
    "md_has_code_block": "Bool",
    "md_has_heading": "Bool",
    "md_parse": "Result",
    "md_render": "String",
    # nat_to
    "nat_to_int": "Int",
    "nat_to_string": "String",
    # option
    "option_and_then": "Option",
    "option_map": "Option",
    # parse
    "parse_bool": "Result",
    "parse_float64": "Result",
    "parse_int": "Result",
    "parse_nat": "Result",
    # regex
    "regex_find": "Result",
    "regex_find_all": "Result",
    "regex_match": "Result",
    "regex_replace": "Result",
    # result
    "result_map": "Result",
    # set_
    "set_add": "Set",
    "set_contains": "Bool",
    "set_new": "Set",
    "set_remove": "Set",
    "set_size": "Int",
    "set_to_array": "Array",
    # string
    "string_char_code": "Nat",
    "string_chars": "Array",
    "string_concat": "String",
    "string_contains": "Bool",
    "string_ends_with": "Bool",
    "string_from_char_code": "String",
    "string_index_of": "Option",
    "string_join": "String",
    "string_length": "Int",
    "string_lines": "Array",
    "string_lower": "String",
    "string_pad_end": "String",
    "string_pad_start": "String",
    "string_repeat": "String",
    "string_replace": "String",
    "string_reverse": "String",
    "string_slice": "String",
    "string_split": "Array",
    "string_starts_with": "Bool",
    "string_strip": "String",
    "string_trim_end": "String",
    "string_trim_start": "String",
    "string_upper": "String",
    "string_words": "Array",
    # to_string
    "to_string": "String",
    # url
    "url_decode": "Result",
    "url_encode": "String",
    "url_join": "String",
    "url_parse": "Result",
}

# Builtins returning FULLY-CONCRETE parameterized types — maps function name
# to (outer_type, (inner_type, ...)) for _get_arg_type_info() and its WASM
# twin _get_arg_type_info_wasm (vera/wasm/inference.py imports this dict, so
# additions fix discovery and call-rewrite atomically).  REGISTRY-COMPLETE
# (#769): exactly the registered builtins whose return is an AdtType with
# type args and no embedded TypeVar, values as the registry's pretty names
# (nested inners like "Array<Json>" parse via _parse_type_name); enforced by
# tests/test_codegen_monomorphize.py::TestBuiltinReturnTables769.  Builtins
# whose return keeps a type var (array_map, map_get, …) must stay OUT —
# they are handled by the generic-return / arg-forwarding resolution.
_BUILTIN_PARAMETERIZED_RETURNS: dict[str, tuple[str, tuple[str, ...]]] = {
    # array
    "array_range": ("Array", ("Int",)),
    # base64
    "base64_decode": ("Result", ("String", "String")),
    # decimal
    "decimal_div": ("Option", ("Decimal",)),
    "decimal_from_string": ("Option", ("Decimal",)),
    # html
    "html_attr": ("Option", ("String",)),
    "html_parse": ("Result", ("HtmlNode", "String")),
    "html_query": ("Array", ("HtmlNode",)),
    # int_to
    "int_to_byte": ("Option", ("Byte",)),
    "int_to_nat": ("Option", ("Nat",)),
    # json
    "json_array_get": ("Option", ("Json",)),
    "json_as_array": ("Option", ("Array<Json>",)),
    "json_as_bool": ("Option", ("Bool",)),
    "json_as_int": ("Option", ("Int",)),
    "json_as_number": ("Option", ("Float64",)),
    "json_as_object": ("Option", ("Map<String, Json>",)),
    "json_as_string": ("Option", ("String",)),
    "json_get": ("Option", ("Json",)),
    "json_get_array": ("Option", ("Array<Json>",)),
    "json_get_bool": ("Option", ("Bool",)),
    "json_get_int": ("Option", ("Int",)),
    "json_get_number": ("Option", ("Float64",)),
    "json_get_string": ("Option", ("String",)),
    "json_keys": ("Array", ("String",)),
    "json_parse": ("Result", ("Json", "String")),
    # md_
    "md_extract_code_blocks": ("Array", ("String",)),
    "md_parse": ("Result", ("MdBlock", "String")),
    # parse
    "parse_bool": ("Result", ("Bool", "String")),
    "parse_float64": ("Result", ("Float64", "String")),
    "parse_int": ("Result", ("Int", "String")),
    "parse_nat": ("Result", ("Nat", "String")),
    # regex
    "regex_find": ("Result", ("Option<String>", "String")),
    "regex_find_all": ("Result", ("Array<String>", "String")),
    "regex_match": ("Result", ("Bool", "String")),
    "regex_replace": ("Result", ("String", "String")),
    # string
    "string_chars": ("Array", ("String",)),
    "string_index_of": ("Option", ("Nat",)),
    "string_lines": ("Array", ("String",)),
    "string_split": ("Array", ("String",)),
    "string_words": ("Array", ("String",)),
    # url
    "url_decode": ("Result", ("String", "String")),
    "url_parse": ("Result", ("UrlParts", "String")),
}


@dataclass(frozen=True)
class MonoContext:
    """Registration metadata for instantiation discovery + substitution.

    Built independently by each consumer — codegen from its layout/signature
    mixin state, the verifier from :class:`~vera.environment.TypeEnv` — but the
    shape is identical so :class:`Monomorphizer`'s leaf logic is shared.  All
    fields are AST-level (no WASM types), which is what lets the verifier import
    this module without dragging in the codegen backend.

    * ``generic_decls`` — generic function name → its ``FnDecl``.
    * ``ctor_to_adt`` — constructor name → owning ADT name.
    * ``ctor_tp_indices`` — constructor name → per-field ADT type-param index
      (``None`` for fields that bind no type param).  Lets sparse constructors
      like ``Err(e)`` map their single field to ``Result``'s *second* type param.
    * ``adt_tp_counts`` — ADT name → number of type parameters.
    * ``type_aliases`` / ``type_alias_params`` — alias name → body ``TypeExpr`` /
      declared alias parameter names (for FnType-alias argument resolution).
    * ``fn_ret_types`` — function name (top-level **and** ``where`` helpers,
      keyed by bare name) → *simple* Vera return-type name, **type args dropped**
      (``Map<String, Int>`` → ``"Map"``; contrast the full names
      ``_get_arg_type_info`` / ``_infer_vera_type_name`` carry).  Codegen builds
      it from its WAT signatures (i64→Int, i32→Bool, f64→Float64) to reproduce
      the prior ``_infer_fncall_vera_type_simple`` behaviour exactly; the
      verifier builds it from declared AST return types, keeping the *more
      precise* name (``Nat``, ``Byte``).  The two value-spaces are deliberately
      related by the fixed collapse ``{Nat→Int, Byte→Bool}`` — the verifier's
      discovered set is a sound superset under that normalization, which the
      #732 differential test maintains (its ``collapse`` table is the one place
      that mapping lives) and pins.
    * ``fn_ret_type_exprs`` — function name (bare-keyed, same as ``fn_ret_types``)
      → declared return **TypeExpr** (type args RETAINED, unlike ``fn_ret_types``).
      Lets discovery recover a user fn's *parameterized* return (`maybe → Option<Decimal>`)
      in `Option<T>` argument position, mirroring the WASM call-rewrite's
      ``_fn_ret_type_exprs`` so the two consultors pick the same clone (#899 issue 1).
      Optional (defaults empty): a consumer that doesn't populate it simply
      loses the user-fn parameterized-return recovery, degrading to the prior
      (bare-name) behaviour rather than erroring.
    """

    generic_decls: dict[str, ast.FnDecl]
    ctor_to_adt: dict[str, str]
    ctor_tp_indices: dict[str, tuple[int | None, ...]]
    adt_tp_counts: dict[str, int]
    type_aliases: dict[str, ast.TypeExpr]
    type_alias_params: dict[str, tuple[str, ...]]
    fn_ret_types: dict[str, str]
    fn_ret_type_exprs: dict[str, ast.TypeExpr] = field(default_factory=dict)


class Monomorphizer:
    """Instantiation discovery + AST substitution over a :class:`MonoContext`.

    Stateless apart from ``ctx``; safe to construct per-pass.  Orchestration
    (the seed walk + transitive worklist, and whether to filter
    constraint-failing instances) is the caller's responsibility — see
    ``MonomorphizationMixin._monomorphize`` (codegen) and the verifier's
    per-instance loop (#732).
    """

    def __init__(self, ctx: MonoContext) -> None:
        self.ctx = ctx

    def collect_calls_in_expr(
        self,
        expr: ast.Expr,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Collect every generic call site reachable from ``expr``.

        Public because it is the shared discovery contract: both codegen
        (Pass 1.5) and the verifier (#732) drive it, and per-monomorphization
        verification is sound only if the verifier discovers a superset of what
        codegen emits.  The walk is TOTAL over the AST — it visits every child
        via dataclass fields — so a generic call nested in ANY form
        (``ArrayLit``, ``IndexExpr``, ``InterpolatedString``, a quantifier, …)
        is discovered, not just the forms an explicit arm happened to list.

        This is byte-identical for compiling programs: a generic call in a form
        codegen can't lower would be a dangling reference, so any program that
        DOES compile already has every generic call in a walked position; the
        total walk only adds coverage for programs that wouldn't compile anyway.
        """
        self._collect_calls(expr, generic_decls, ctor_to_adt, instances)

    def collect_calls_in_node(
        self,
        fn: ast.FnDecl,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Collect generic calls reachable from a whole ``FnDecl`` — its body,
        its contract predicates, AND its ``where`` helpers.

        This is the function-level shared discovery contract.  A generic called
        only from a ``requires`` / ``ensures`` / ``decreases`` clause (which Vera
        lowers to a runtime contract check) or only from a ``where`` helper body
        is still emitted by codegen and invoked at runtime, so codegen's Pass 1.5
        and the verifier (#732) must BOTH seed from this node-level walk — not
        just ``decl.body``.  Walking only the body makes codegen miss the clone
        (a ``CodegenSkip`` at run time) and diverge from the verifier, which does
        walk contracts and helpers (PR #767 review).
        """
        self.collect_calls_in_expr(
            fn.body, generic_decls, ctor_to_adt, instances,
        )
        for contract in fn.contracts:
            # Requires/Ensures/Invariant carry a single `.expr`; Decreases
            # carries `.exprs` (a tuple of termination measures).
            preds = list(getattr(contract, "exprs", ()) or ())
            single = getattr(contract, "expr", None)
            if single is not None:
                preds.append(single)
            for pred in preds:
                self.collect_calls_in_expr(
                    pred, generic_decls, ctor_to_adt, instances,
                )
        for wfn in fn.where_fns or ():
            self.collect_calls_in_node(
                wfn, generic_decls, ctor_to_adt, instances,
            )

    def _collect_calls(
        self,
        node: object,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Total AST recursion underlying :meth:`collect_calls_in_expr`."""
        # #774: a qualified call `m::g(…)` to an imported generic is an
        # ``ast.ModuleCall``, not a ``FnCall`` — discover it identically (same
        # arg-driven type inference) so the importer monomorphizes the same
        # instantiation for both call forms.  Keyed on ``generic_decls``: the
        # caller merges imported (unshadowed) generics into that dict, so a
        # ModuleCall only matches once its target is a known generic.
        if isinstance(node, (ast.FnCall, ast.ModuleCall)) and (
            node.name in generic_decls
        ):
            decl = generic_decls[node.name]
            type_args = self._infer_type_args_from_args(
                decl, node.args, ctor_to_adt, generic_decls,
            )
            if type_args is not None:
                instances[node.name].add(type_args)
        # #913: a generic invoked via the ``|>`` pipe — ``x |> g(…)`` — desugars
        # to ``g(x, …)`` at BOTH the checker (`_check_pipe`) and codegen
        # (`_translate_binary`) boundaries, prepending the piped LHS as the
        # call's FIRST argument.  Discovery must reconstruct that same argument
        # list, or the bare RHS ``FnCall``/``ModuleCall`` (whose own `args`
        # omit the piped value) fails to bind the type variable that the piped
        # value supplies — so no ``g$Type`` clone is emitted and codegen lowers
        # the pipe to a call on a non-existent function (the enclosing fn is
        # dropped at run).  The RHS itself is walked by the generic field
        # recursion below, so an inner generic call reachable through the RHS
        # is still discovered; this branch only adds the pipe-desugared
        # instantiation.
        if (
            isinstance(node, ast.BinaryExpr)
            and node.op == ast.BinOp.PIPE
            and isinstance(node.right, (ast.FnCall, ast.ModuleCall))
            and node.right.name in generic_decls
        ):
            decl = generic_decls[node.right.name]
            piped_args = (node.left,) + node.right.args
            type_args = self._infer_type_args_from_args(
                decl, piped_args, ctor_to_adt, generic_decls,
            )
            if type_args is not None:
                instances[node.right.name].add(type_args)
        if isinstance(node, ast.Node):
            for f in fields(node):
                if f.name == "span":
                    continue
                self._collect_calls(
                    getattr(node, f.name), generic_decls, ctor_to_adt,
                    instances,
                )
        elif isinstance(node, (tuple, list)):
            for item in node:
                self._collect_calls(
                    item, generic_decls, ctor_to_adt, instances,
                )

    def _infer_type_args_from_call(
        self,
        decl: ast.FnDecl,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer concrete type variable bindings from a call's arguments.

        Returns a tuple of concrete type names, one per forall_var, or
        None if inference fails.
        """
        return self._infer_type_args_from_args(
            decl, call.args, ctor_to_adt, generic_decls,
        )

    def _infer_type_args_from_args(
        self,
        decl: ast.FnDecl,
        args: tuple[ast.Expr, ...],
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer concrete type variable bindings from an argument tuple.

        The arg-driven core shared by ``FnCall`` and ``ModuleCall`` (#774): a
        qualified call to an imported generic carries the same positional
        arguments, so the type-parameter inference is identical to a bare call.

        Returns a tuple of concrete type names, one per forall_var, or
        None if inference fails.
        """
        forall_vars = decl.forall_vars
        if not forall_vars:
            return None

        # Type vars carrying an ability bound (`where Eq<T>`).  For these, a
        # `ConstructorCall` argument to a direct `@T` parameter must keep its
        # type argument (`Box<String>`, not bare `Box`) so the clone name, the
        # substituted slot type in the clone body, AND the E613 gate all see the
        # concrete field type — exactly as the slot-ref call form already does
        # (#772).  Unconstrained vars stay bare: a `Box<T>` clone is a uniform
        # pointer, so keeping one `id$Box` for every instantiation avoids
        # needless clone splitting for generics whose behaviour is type-blind.
        constrained_vars = frozenset(
            c.type_var for c in (decl.forall_constraints or ())
        )

        mapping: dict[str, str] = {}
        # #898: per-constrained-forall-var accumulator of a sparse
        # multi-parameter ADT's partial per-parameter recovery, MERGED across
        # every constructor argument bound to that var.  Each entry is
        # (base_name, [name-or-None per ADT type parameter]); `MkErr(5)` fills
        # one slot, `MkOk("x")` fills the other, so the two together yield the
        # fully-determined `Res<String, Int>` the checker's cross-argument merge
        # (`merge_inferred_types`) already accepted — keeping the monomorphizer
        # in lockstep so the emitted clone matches the type-checked call.
        partial_adt: dict[str, tuple[str, list[str | None]]] = {}
        for param_te, arg in zip(decl.params, args):
            self._unify_param_arg(param_te, arg, forall_vars, ctor_to_adt,
                                  mapping, generic_decls, constrained_vars,
                                  partial_adt)

        # Materialise any merged sparse-ADT recovery.
        #
        # * Fully determined (every parameter now known across all arguments):
        #   promote the bare name to the full parameterised name so the E613
        #   gate and clone body see the concrete field types, and the emitted
        #   clone matches the type-checked call.
        # * Partially determined (a genuinely free parameter remains — the
        #   single-argument `id1(MkErr(5))` shape): materialise a name that
        #   still carries the RECOVERED components, with each free slot marked
        #   by the reserved `?` sentinel (`Res<?, Int>`).  This never names an
        #   emitted clone (the instance is always rejected by the ability gate),
        #   but it lets the gate distinguish an under-determined type whose
        #   known components ARE Eq (→ clearer E619, annotate the free param)
        #   from one whose known component is already non-Eq (→ accurate E613,
        #   annotation cannot help) — #898 diagnostic-accuracy fix.
        for tv, (base_name, slots) in partial_adt.items():
            if all(s is not None for s in slots):
                resolved = [s for s in slots if s is not None]
                mapping[tv] = f"{base_name}<{', '.join(resolved)}>"
            elif tv in constrained_vars:
                rendered = [s if s is not None else _FREE_TYPE_PARAM
                            for s in slots]
                mapping[tv] = f"{base_name}<{', '.join(rendered)}>"

        # Check all type vars are resolved; default unresolved phantom vars to
        # Bool (NOT Unit — see the rationale just below: Bool has an i32 repr)
        result = []
        for tv in forall_vars:
            if tv not in mapping:
                # Phantom type variable (e.g. E in result_unwrap_or(Ok(x), d))
                # — the generated WASM is identical regardless of this type.
                # Use Bool (i32) rather than Unit (no WASM repr) so the
                # monomorphized body can still compile unused branches.
                mapping[tv] = "Bool"
            result.append(mapping[tv])
        return tuple(result)

    def _unify_param_arg(
        self,
        param_te: ast.TypeExpr,
        arg: ast.Expr,
        forall_vars: tuple[str, ...],
        ctor_to_adt: dict[str, str],
        mapping: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
        constrained_vars: frozenset[str] = frozenset(),
        partial_adt: dict[str, tuple[str, list[str | None]]] | None = None,
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars."""
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg(
                param_te.base_type, arg, forall_vars, ctor_to_adt, mapping,
                generic_decls, constrained_vars, partial_adt,
            )
            return

        if not isinstance(param_te, ast.NamedType):
            return

        if param_te.name in forall_vars:
            # Direct type variable — infer from argument
            vera_type = self._infer_vera_type_name(
                arg, ctor_to_adt, generic_decls)
            if (param_te.name in constrained_vars
                    and isinstance(arg, ast.ConstructorCall)):
                # `_infer_vera_type_name` drops the type argument for a
                # `ConstructorCall` (returns bare `Box`).  For a CONSTRAINED
                # var the type argument is load-bearing (the ability check and
                # the clone body's structural `==` both need it), so recover the
                # parameterized name via `_get_arg_type_info` — the same routine
                # the `Option<T>` parameterized path uses (#772).
                info = self._get_arg_type_info(arg, ctor_to_adt)
                if info is not None:
                    base_name, arg_names = info
                    if arg_names and all(a is not None for a in arg_names):
                        resolved = [a for a in arg_names if a is not None]
                        vera_type = f"{base_name}<{', '.join(resolved)}>"
                    elif arg_names and partial_adt is not None:
                        # #898: PARTIAL recovery — this constructor pins only
                        # some of the ADT's type parameters (`MkErr(5)` fills
                        # `B`, not `A`).  Accumulate the per-slot info under this
                        # forall var, MERGING with any sibling argument's
                        # recovery (`MkOk("x")` fills `A`), so the fully-
                        # determined `Res<String, Int>` is materialised after
                        # every argument is seen.  A later slot overwrites None,
                        # never a concrete name (siblings agree on shared slots
                        # because the checker already accepted the call — a
                        # genuine conflict is an E205 there, never reaching mono).
                        prev = partial_adt.get(param_te.name)
                        if prev is None or prev[0] != base_name:
                            slots: list[str | None] = list(arg_names)
                            partial_adt[param_te.name] = (base_name, slots)
                        else:
                            slots = prev[1]
                            for i, name in enumerate(arg_names):
                                if name is not None and i < len(slots):
                                    slots[i] = name
            if vera_type and param_te.name not in mapping:
                mapping[param_te.name] = vera_type
            return

        # Parameterized type like Option<T> — match type args
        if param_te.type_args:
            # Handle type alias for FnType matched against a callable
            # arg — either an AnonFn literal or a SlotRef whose static
            # type is itself an FnType alias.  #604: pre-fix, only the
            # AnonFn branch fired; SlotRef-typed-as-FnType-alias args
            # like ``@Doubler.0`` skipped this branch and left the
            # ``B`` type var unbound, hitting the ``"Bool"`` phantom-
            # var default at result-building time and producing wrong
            # mono suffixes.  The helper now resolves either shape.
            alias_concrete = self._infer_fn_alias_type_args(
                param_te, arg,
            )
            if alias_concrete is not None:
                for param_ta, concrete_name in zip(
                    param_te.type_args, alias_concrete,
                ):
                    self._unify_type_arg_pair(
                        param_ta, concrete_name, forall_vars, mapping,
                    )
                return

            arg_info = self._get_arg_type_info(arg, ctor_to_adt)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    # arg_ta_name is None for unknown type-param positions
                    # (e.g. T in Err(e) where only E can be inferred from Err).
                    if arg_ta_name is not None:
                        self._unify_type_arg_pair(
                            param_ta, arg_ta_name, forall_vars, mapping,
                        )

    @staticmethod
    def _unify_type_arg_pair(
        param_ta: ast.TypeExpr,
        arg_name: str,
        forall_vars: tuple[str, ...],
        mapping: dict[str, str],
    ) -> None:
        """Recursively unify ONE parameter type-argument against a concrete
        type-argument NAME, binding forall vars at any nesting depth (#769
        gap 2): ``Option<T>`` vs ``"Option<Int>"`` binds ``T = "Int"``, and so
        does ``Array<Option<T>>`` vs ``"Array<Option<Int>>"`` — the pre-#769
        zip bound only when the IMMEDIATE type argument was the variable
        itself, so any deeper var fell to the ``Bool`` phantom default.

        First binding wins (``mapping`` is never overwritten), matching
        ``_unify_param_arg``'s outer behavior.  Static and self-contained so
        the WASM call-rewrite twin (``_unify_param_arg_wasm``,
        vera/wasm/calls.py) calls THIS implementation — the two clone-name
        consultors bind identically by construction.
        """
        if isinstance(param_ta, ast.RefinementType):
            param_ta = param_ta.base_type
        if not isinstance(param_ta, ast.NamedType):
            return
        if param_ta.name in forall_vars:
            if param_ta.name not in mapping:
                mapping[param_ta.name] = arg_name
            return
        if not param_ta.type_args:
            return
        parsed = Monomorphizer._parse_type_name(arg_name)
        if parsed.name != param_ta.name or not parsed.type_args:
            return
        for p_sub, a_sub in zip(param_ta.type_args, parsed.type_args):
            if isinstance(a_sub, ast.NamedType):
                Monomorphizer._unify_type_arg_pair(
                    p_sub, Monomorphizer._format_type_name(a_sub),
                    forall_vars, mapping,
                )

    def _infer_vera_type_name(
        self,
        expr: ast.Expr,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> str | None:
        """Infer the simple Vera type name of an expression."""
        if isinstance(expr, ast.IntLit):
            return "Int"
        if isinstance(expr, ast.BoolLit):
            return "Bool"
        if isinstance(expr, ast.FloatLit):
            return "Float64"
        if isinstance(expr, ast.UnitLit):
            return "Unit"
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                # Include type args for parameterized types like Map<String, Int>
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(self._format_type_name(ta))
                    else:
                        return expr.type_name
                return f"{expr.type_name}<{', '.join(arg_names)}>"
            return expr.type_name
        if isinstance(expr, ast.ConstructorCall):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.NullaryConstructor):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (ast.BinOp.EQ, ast.BinOp.NEQ, ast.BinOp.LT,
                           ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE,
                           ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "Bool"
            return self._infer_vera_type_name(
                expr.left, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NOT:
                return "Bool"
            return self._infer_vera_type_name(
                expr.operand, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.IfExpr):
            return self._infer_vera_type_name(
                expr.then_branch.expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.StringLit):
            return "String"
        if isinstance(expr, ast.InterpolatedString):
            return "String"
        if isinstance(expr, ast.ArrayLit):
            return "Array"
        if isinstance(expr, ast.FnCall) and generic_decls:
            return self._infer_fncall_vera_type(
                expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type_simple(expr)
        return None

    def _infer_fncall_vera_type(
        self,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl],
    ) -> str | None:
        """Infer the Vera return type of a function call.

        For generic calls, infers type variable bindings from arguments,
        then substitutes into the return TypeExpr.
        """
        # #769 logic-arm parity with the WASM call-rewrite chain
        # (InferenceMixin._infer_fncall_vera_type, vera/wasm/inference.py):
        # apply_fn / async / await need call-shape context no fixed table can
        # hold, so each side carries the same arm — a name inferred here must
        # equal the rewrite's, or the discovered clone dangles and the caller
        # is skipped (E602).  These names cannot be user-redefined (E151), so
        # the arms fire only for the real builtins.
        if call.name == "apply_fn" and call.args:
            ret_te: ast.TypeExpr | None = self._closure_arg_return_te(
                call.args[0])
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if isinstance(ret_te, ast.NamedType):
                return self._format_type_name(ret_te)
        if call.name == "async" and call.args:
            inner = self._infer_vera_type_name(
                call.args[0], ctor_to_adt, generic_decls)
            return f"Future<{inner}>" if inner else "Future"
        if call.name == "await" and call.args:
            inner = self._infer_vera_type_name(
                call.args[0], ctor_to_adt, generic_decls)
            if inner and inner.startswith("Future<") and inner.endswith(">"):
                return inner[7:-1]
            return inner
        if call.name in generic_decls:
            decl = generic_decls[call.name]
            type_args = self._infer_type_args_from_call(
                decl, call, ctor_to_adt, generic_decls,
            )
            if type_args and decl.forall_vars:
                mapping = dict(zip(decl.forall_vars, type_args))
                ret_te = decl.return_type
                # Unwrap an inline refinement to its base, mirroring the
                # rewrite side's generic branch (vera/wasm/inference.py) —
                # the two consultors must land on the same name (PR #972
                # review; both previously agreed via the WAT collapse only
                # by coincidence for refined returns).
                if isinstance(ret_te, ast.RefinementType):
                    ret_te = ret_te.base_type
                if isinstance(ret_te, ast.NamedType):
                    return mapping.get(ret_te.name, ret_te.name)
        return self._infer_fncall_vera_type_simple(call)

    def _closure_arg_return_te(self, arg: ast.Expr) -> ast.TypeExpr | None:
        """Declared return TypeExpr of a callable argument (#769).

        The discovery-side mirror of the rewrite chain's
        ``_closure_arg_return_type`` dispatch: an inline ``AnonFn`` yields its
        declared return type; a ``SlotRef`` typed as an ``FnType`` alias
        resolves TRANSITIVELY through the shared ``resolve_fn_type_alias``
        (#867) to the terminal ``FnType``'s return type.
        """
        if isinstance(arg, ast.AnonFn):
            return arg.return_type
        if isinstance(arg, ast.SlotRef):
            fn_te = resolve_fn_type_alias(
                ast.NamedType(name=arg.type_name, type_args=arg.type_args),
                self.ctx.type_aliases,
                self.ctx.type_alias_params,
            )
            if fn_te is not None:
                return fn_te.return_type
        return None

    def _infer_fncall_vera_type_simple(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type from registered function signatures.

        Builtin handle types (Decimal, Map, Set, …) are resolved from the
        static table first; everything else comes from ``ctx.fn_ret_types``,
        which each consumer pre-populates (codegen from its WAT signatures,
        the verifier from declared AST return types).
        """
        # A name registered in fn_ret_types is a REAL declaration in this
        # program — a user fn, or a user OVERRIDE of an E151-exempt prelude
        # combinator (#815: option_map, the json_* family, html_attr) — and
        # its declared type wins over the builtin table (the #908 show/hash
        # gate, generalised; adversarial panel, PR #972).  Opaque builtins
        # (string_chars, decimal_*, …) are never registered there, so they
        # fall through to the table as before.
        declared = self.ctx.fn_ret_types.get(call.name)
        if declared is not None:
            return declared
        return _BUILTIN_VERA_RETURN_TYPES.get(call.name)

    @staticmethod
    def _parse_type_name(name: str) -> ast.NamedType:
        """Parse a full type name string into a NamedType AST node.

        E.g. "Map<String, Int>" → NamedType("Map", (NamedType("String"),
        NamedType("Int"))).  Handles nested types like
        "Map<String, Array<Int>>".
        """
        if "<" not in name:
            return ast.NamedType(name=name, type_args=None)
        base = name[:name.index("<")]
        inner = name[name.index("<") + 1:-1]  # strip outer < >
        # Split at top-level commas (respecting nesting)
        args: list[str] = []
        depth = 0
        current: list[str] = []
        for ch in inner:
            if ch == "<":
                depth += 1
                current.append(ch)
            elif ch == ">":
                depth -= 1
                current.append(ch)
            elif ch == "," and depth == 0:
                args.append("".join(current).strip())
                current = []
            else:
                current.append(ch)
        if current:
            args.append("".join(current).strip())
        type_args = tuple(
            Monomorphizer._parse_type_name(a) for a in args
        )
        return ast.NamedType(name=base, type_args=type_args)

    @staticmethod
    def _format_type_name(te: ast.NamedType) -> str:
        """Format a NamedType as a full type name including type args.

        E.g. NamedType("Map", (NamedType("String"), NamedType("Int")))
        becomes "Map<String, Int>".

        Note: duplicated in InferenceMixin._format_named_type (inference.py).
        Both must remain in sync — the mixin architecture prevents sharing.
        """
        if not te.type_args:
            return te.name
        arg_names = []
        for ta in te.type_args:
            if isinstance(ta, ast.NamedType):
                arg_names.append(Monomorphizer._format_type_name(ta))
            else:
                return te.name
        return f"{te.name}<{', '.join(arg_names)}>"

    def _get_arg_type_info(
        self, expr: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> tuple[str, tuple[str | None, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression.

        Used to match parameterized types like Option<T> against
        concrete arguments like @Option<Int>.0.  Type arg entries may be
        None for positions that cannot be inferred from the argument (e.g.
        T in Err(e) where only E is resolved from Err).
        """
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(self._format_type_name(ta))
                    else:
                        return None
                return (expr.type_name, tuple(arg_names))
            return (expr.type_name, ())
        if isinstance(expr, ast.ConstructorCall):
            adt_name = ctor_to_adt.get(expr.name)
            if adt_name:
                # Use the per-field ADT type-param index mapping when available.
                # This correctly handles sparse constructors like Err(e) whose
                # single field maps to Result's *second* type param (E, index 1),
                # not the first (T, index 0) as naïve positional zipping implies.
                field_tp_idx = self.ctx.ctor_tp_indices.get(expr.name)
                adt_tp_count = self.ctx.adt_tp_counts.get(adt_name, 0)
                if field_tp_idx is not None and adt_tp_count > 0:
                    result_tps: list[str | None] = [None] * adt_tp_count
                    for field_i, tp_idx in enumerate(field_tp_idx):
                        if tp_idx is not None and field_i < len(expr.args):
                            t = self._infer_vera_type_name(
                                expr.args[field_i], ctor_to_adt)
                            if t is not None:
                                result_tps[tp_idx] = t
                            # If t is None, leave position as None (unknown)
                    return (adt_name, tuple(result_tps))
                # Fall back to positional inference for constructors without
                # mapping info (e.g. user-defined ADTs not yet registered).
                arg_types = []
                for a in expr.args:
                    t = self._infer_vera_type_name(a, ctor_to_adt)
                    if t:
                        arg_types.append(t)
                    else:
                        return None
                return (adt_name, tuple(arg_types))
        if isinstance(expr, ast.ArrayLit):
            # Infer the element type from the first element — FULL-DEPTH when
            # the element itself carries type-arg info (a nested literal or a
            # constructor call), so ``Array<Array<E>>`` binds ``E`` from
            # ``[[1, 2]]`` and ``Array<Option<T>>`` binds ``T`` from
            # ``[Some(1)]`` via the recursive unifier (#769 gap 2).  The WASM
            # twin's ArrayLit branch (vera/wasm/inference.py) mirrors this
            # exactly — element-name granularity is part of the clone-name
            # agreement contract (#772), so the two sides must move together.
            if expr.elements:
                elem_type = self._array_elem_type_name(
                    expr.elements[0], ctor_to_adt,
                )
                if elem_type:
                    return ("Array", (elem_type,))
            return ("Array", ())
        if isinstance(expr, ast.FnCall):
            # Builtins returning parameterized types (e.g. decimal_div →
            # Option<Decimal>).  Gated on non-registration: a name in
            # fn_ret_types is a real decl — possibly a user override of an
            # E151-exempt prelude combinator (#815) — whose DECLARED return
            # must win (it resolves via fn_ret_type_exprs below; adversarial
            # panel, PR #972).
            if expr.name not in self.ctx.fn_ret_types:
                param_ret = _BUILTIN_PARAMETERIZED_RETURNS.get(expr.name)
                if param_ret is not None:
                    return param_ret
            if expr.name in ("array_concat", "array_append",
                             "array_slice", "array_filter"):
                if expr.args:
                    return self._get_arg_type_info(expr.args[0], ctor_to_adt)
            # #899 issue 1: a NON-generic user fn returning a parameterized type
            # (`maybe → Option<Decimal>`) in `Option<T>` position must expose its
            # type args so `T` binds from THIS argument.  Mirrors the WASM
            # call-rewrite `_get_arg_type_info_wasm` FnCall branch
            # (vera/wasm/inference.py) so discovery and call-rewrite pick the
            # same clone — else discovery emits `first_opt$Bool` while the call
            # site references `first_opt$Decimal`, a dangling reference (E602).
            # GENERIC calls are excluded: their declared return is over the
            # callee's OWN type vars, not concrete types, so their type args
            # would bind a phantom var — they fall through to the generic-return
            # resolution instead (same exclusion the call-rewrite side applies).
            if expr.name in (self.ctx.generic_decls or {}):
                return None
            ret_te = self.ctx.fn_ret_type_exprs.get(expr.name)
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if isinstance(ret_te, ast.NamedType) and ret_te.type_args:
                ta_names: list[str | None] = []
                for ta in ret_te.type_args:
                    if isinstance(ta, ast.NamedType) and not ta.type_args:
                        ta_names.append(self._format_type_name(ta))
                    else:
                        ta_names.append(None)
                return (ret_te.name, tuple(ta_names))
        return None

    def _array_elem_type_name(
        self, elem: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> str | None:
        """FULL-DEPTH type name of an array-literal element (#769 gap 2).

        Prefers the parameterized recovery (``Some(1)`` → ``"Option<Int>"``,
        ``[1, 2]`` → ``"Array<Int>"``) when every type-arg position is known;
        falls back to the simple name (``"Int"``, ``"String"``) otherwise —
        the pre-#769 behavior, so under-determined elements degrade rather
        than mis-bind.
        """
        info = self._get_arg_type_info(elem, ctor_to_adt)
        if info is not None:
            outer, args = info
            if args and all(a is not None for a in args):
                return f"{outer}<{', '.join(a for a in args if a is not None)}>"
        return self._infer_vera_type_name(elem, ctor_to_adt)

    def full_arg_type_name(
        self, expr: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> str | None:
        """Fully-qualified Vera type name of an argument expression (#932).

        The DERIVABILITY-decision counterpart of the one-level names
        :meth:`_get_arg_type_info` / :meth:`_infer_vera_type_name` recover.
        Recurses through nested ``ConstructorCall`` fields so every level's type
        argument is reconstructed: a `Cons(Cons(1, Nil), Nil)` operand yields the
        FULLY-qualified ``List<List<Int>>`` rather than the one-level
        ``List<List>`` the flat recovery produces (the residue that the
        codegen-side Eq-derivability gate then treats as a lost-type-arg clone
        and spuriously E613s).

        This is the mono-side mirror of ``OperatorsMixin._full_ctor_type_name``
        (vera/wasm/operators.py, #923's DIRECT-``==`` recovery).  It is consumed
        ONLY for the Eq-derivability decision (`_check_constraints`) — the
        mangled CLONE NAME codegen emits and looks up stays the truncated
        one-level name (`eq2$List<List>`) that `_get_arg_type_info` produces, so
        the clone-mangling contract `_unify_param_arg` relies on is unchanged
        (the #772 hard constraint).

        Falls back to the bare :meth:`_infer_vera_type_name` for a
        non-``ConstructorCall`` operand (a nested `[1]` bottoms out at the bare
        `Array`, a nullary `Nil` at the bare `List`).  Returns ``None`` only when
        the base ADT name itself cannot be resolved; a field whose type argument
        cannot be inferred leaves that position bare, matching the lost-type-arg
        shape the derivability gate already handles.
        """
        if not isinstance(expr, ast.ConstructorCall):
            return self._infer_vera_type_name(expr, ctor_to_adt)
        base = ctor_to_adt.get(expr.name)
        if base is None:
            return None
        tp_indices = self.ctx.ctor_tp_indices.get(expr.name)
        tp_count = self.ctx.adt_tp_counts.get(base, 0)
        if not tp_indices or tp_count == 0:
            return base
        slots: list[str | None] = [None] * tp_count
        for field_i, tp_idx in enumerate(tp_indices):
            if tp_idx is not None and field_i < len(expr.args):
                slots[tp_idx] = self.full_arg_type_name(
                    expr.args[field_i], ctor_to_adt,
                )
        if all(s is not None for s in slots):
            return f"{base}<{', '.join(s for s in slots if s is not None)}>"
        return base

    def _resolve_arg_fn_shape(
        self,
        arg: ast.Expr,
    ) -> tuple[tuple[ast.TypeExpr, ...], ast.TypeExpr] | None:
        """Return ``(param_types, return_type)`` for an arg that's callable.

        Two arg shapes resolve:

        * ``AnonFn`` literal — its declared params + return type.
        * ``SlotRef`` whose static type is an FnType alias (e.g.
          ``@Doubler.0`` where ``type Doubler = fn(Int -> Int)``) —
          the alias's resolved params + return type.  For a
          *parameterised* alias like
          ``type Mapper<T> = fn(T -> T) effects(pure)``, the
          ``SlotRef``'s type-args are substituted into the alias body
          first so ``@Mapper<Int>.0`` returns
          ``(NamedType("Int"),), NamedType("Int")`` rather than the
          unsubstituted ``T``.  Without substitution, the downstream
          ``_infer_fn_alias_type_args`` matcher would bind alias-local
          names instead of concrete ones, producing mono suffixes
          like ``option_map$T_JT`` rather than ``option_map$Int_JInt``
          (CR-4 on PR #659).

        Returns ``None`` for any other arg shape.  Used by
        :meth:`_infer_fn_alias_type_args` to bind generic type variables
        from a closure-shaped argument uniformly across both forms.

        Fixes #604: pre-fix, only the AnonFn form was resolved.  When a
        prelude generic like ``option_map<A, B>(@Option<A>, @OptionMapFn<A, B>)``
        was called with a ``SlotRef`` typed as an FnType alias instead
        of an inline ``AnonFn``, ``B`` failed to bind and defaulted to
        ``Bool`` (the phantom-var fallback in :meth:`_infer_type_args_from_call`),
        producing the wrong mono suffix (``option_map$Int_JBool``) and
        an ``indirect call type mismatch`` trap at runtime.
        """
        if isinstance(arg, ast.AnonFn):
            return (tuple(arg.params), arg.return_type)
        if isinstance(arg, ast.SlotRef):
            # Resolved transitively through the alias chain via the
            # shared resolver (#867 / PR #880 review — the single-hop
            # lookup here made a two-hop-alias-typed closure slot fail
            # shape resolution, so a closure-bound type param fell to
            # the phantom-var default: wrong mono suffix, WASM trap).
            # The resolver substitutes the SlotRef's type_args into a
            # parameterised alias's body per hop (CR-5 on PR #659);
            # arity-mismatch on parameterised aliases is rejected
            # upstream by the type checker ([E133], #660).
            fn_type = resolve_fn_type_alias(
                ast.NamedType(name=arg.type_name, type_args=arg.type_args),
                self.ctx.type_aliases,
                self.ctx.type_alias_params,
            )
            if fn_type is not None:
                return (tuple(fn_type.params), fn_type.return_type)
        return None

    def _infer_fn_alias_type_args(
        self,
        param_te: ast.NamedType,
        arg: ast.Expr,
    ) -> tuple[str, ...] | None:
        """Infer concrete types for a type alias's params from a callable arg.

        When ``param_te`` is e.g. ``NamedType("OptionMapFn", [A, B])``
        which aliases ``fn(A -> B)``, and the argument is callable (an
        ``AnonFn`` literal or a ``SlotRef`` typed as an FnType alias)
        with concrete param/return types, infer one concrete type name
        per alias type parameter.

        Returns a tuple of concrete type names aligned to the alias's
        type parameters, or ``None`` if inference fails.
        """
        arg_shape = self._resolve_arg_fn_shape(arg)
        if arg_shape is None:
            return None
        arg_params, arg_return = arg_shape

        type_aliases = self.ctx.type_aliases
        type_alias_params = self.ctx.type_alias_params

        alias_params = type_alias_params.get(param_te.name)
        if (
            not alias_params
            or not param_te.type_args
            or len(alias_params) != len(param_te.type_args)
        ):
            return None

        # Resolve the param alias's body transitively (#867 / PR #880
        # review): the HOF's declared fn param may itself be an alias
        # chain (`type MapFn2<X, Y> = MapFn<X, Y>;`).  Resolving the
        # chain instantiated at the alias's *own* param names keeps the
        # terminal FnType body expressed in `alias_params` names —
        # including across renaming hops — so the positional matching
        # below is untouched.
        alias_te = resolve_fn_type_alias(
            ast.NamedType(
                name=param_te.name,
                type_args=tuple(
                    ast.NamedType(name=p, type_args=None)
                    for p in alias_params
                ),
            ),
            type_aliases,
            type_alias_params,
        )
        if alias_te is None:
            return None

        # Match the FnType body against the arg's shape to build an
        # alias-local mapping:  alias_param_name -> concrete_type_name
        alias_mapping: dict[str, str] = {}

        # Match parameter types positionally
        for fn_param_te, arg_param_te in zip(
            alias_te.params, arg_params,
        ):
            if (
                isinstance(fn_param_te, ast.NamedType)
                and fn_param_te.name in alias_params
                and isinstance(arg_param_te, ast.NamedType)
            ):
                alias_mapping[fn_param_te.name] = arg_param_te.name

        # Match return type
        ret = alias_te.return_type
        if isinstance(ret, ast.NamedType) and ret.name in alias_params:
            if isinstance(arg_return, ast.NamedType):
                alias_mapping[ret.name] = arg_return.name
            elif isinstance(arg_return, ast.FnType):
                # Return type is itself a FnType — map to "Fn"
                alias_mapping[ret.name] = "Fn"
        # Handle ADT return types like Option<B> where B is an alias param
        if isinstance(ret, ast.NamedType) and ret.type_args:
            for ret_ta in ret.type_args:
                if (
                    isinstance(ret_ta, ast.NamedType)
                    and ret_ta.name in alias_params
                    and isinstance(arg_return, ast.NamedType)
                ):
                    # For Option<B> matched against Option<Int>, extract
                    # B from the arg's return type args
                    if arg_return.type_args:
                        idx = [
                            i for i, rta in enumerate(ret.type_args)
                            if (isinstance(rta, ast.NamedType)
                                and rta.name == ret_ta.name)
                        ]
                        if idx:
                            pos = idx[0]
                            if pos < len(arg_return.type_args):
                                art = arg_return.type_args[pos]
                                if isinstance(art, ast.NamedType):
                                    alias_mapping[ret_ta.name] = art.name

        # Produce result in alias param order
        result: list[str] = []
        for ap in alias_params:
            if ap not in alias_mapping:
                return None
            result.append(alias_mapping[ap])
        return tuple(result)

    @staticmethod
    def _mangle_fn_name(name: str, concrete_types: tuple[str, ...]) -> str:
        """Produce a mangled name for a monomorphized function.

        Example: identity + ("Int",) -> "identity$Int"
        Example: swap + ("Int", "Bool") -> "swap$Int_JBool"
        Example: option_unwrap_or + ("Map<String, Int>",)
                 -> "option_unwrap_or$Map_LString_CInt_R"

        INJECTIVE over (name, type-arg vector), #775.  Each component is
        escaped by :func:`mangle_type_name` (itself injective — see its
        docstring) and the vector is joined with ``_J``.  ``_J`` can never
        be *produced* by the escape: every ``_`` in escaped output starts
        one of the codes ``__``/``_L``/``_R``/``_C``/``_S``, so during the
        left-to-right decode a ``_J`` at a code boundary is unambiguously a
        separator (a literal ``_J`` in a type name escapes to ``__J``,
        whose leading ``__`` is consumed as one code first).  Splitting on
        boundary-``_J`` therefore recovers the exact component vector, and
        each component un-escapes uniquely — no two distinct instantiation
        vectors share a symbol.  ``name`` never contains ``$`` (Vera
        identifiers can't lex it), so the prefix splits off unambiguously
        at the first ``$``.

        Collision classes this kills (both produced duplicate WAT ``func``
        identifiers pre-fix): parameterized built-in vs flat user ADT
        (``g<Map<String, Int>>`` / ``g<Map_String_Int>`` both mangled to
        ``g$Map_String_Int``) and multi-parameter joins across the ``_``
        boundary (``g<A_B, C>`` / ``g<A, B_C>`` both ``g$A_B_C``).

        Determinism: a pure string map of the (already canonical,
        deterministically ordered) instantiation vector — stable across
        runs and platforms.  DESIGN.md principle 1 (checkability: the
        injectivity argument is mechanical, with no reliance on
        bracket-balance properties of the inputs) and principle 3 (one
        canonical form: one shared escape for every type name embedded in
        a WAT symbol) drove the encoding choice.
        """
        suffix = "_J".join(mangle_type_name(ct) for ct in concrete_types)
        return f"{name}${suffix}"

    def monomorphize_fn(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
    ) -> ast.FnDecl:
        """Create a monomorphized copy of a generic function.

        Public: the shared substitution contract called by both codegen and the
        verifier (#732).  Needs no ``ctx`` beyond ``decl`` + ``concrete_types``,
        so a discovery-time ``Monomorphizer`` can be reused at verify time.

        Replaces type variables with concrete types throughout the AST
        and mangles the function name.

        When distinct type variables map to the same concrete type
        (e.g. A→Int, B→Int), De Bruijn indices in slot references
        must be adjusted because formerly separate namespaces merge.
        """
        assert decl.forall_vars is not None  # noqa: S101
        mapping = dict(zip(decl.forall_vars, concrete_types))
        mangled = self._mangle_fn_name(decl.name, concrete_types)

        # Scope-aware De Bruijn reindexing (#769 gap 3): resolve every
        # SlotRef against the full binding scope at its reference site and
        # recompute its index in the collapsed (post-substitution) namespace.
        reindex = self._compute_scoped_reindex(decl, mapping)

        # Substitute type variables in the entire FnDecl
        substituted = self._substitute_in_ast(decl, mapping, reindex)
        assert isinstance(substituted, ast.FnDecl)  # noqa: S101

        # Override name and clear forall_vars/constraints
        return replace(
            substituted, name=mangled,
            forall_vars=None, forall_constraints=None,
        )

    def _substituted_slot_name(
        self, te: ast.TypeExpr, mapping: dict[str, str],
    ) -> str | None:
        """Full-depth canonical slot name of ``te`` AFTER type-variable
        substitution — the name this binder carries in the clone."""
        return type_expr_slot_name(self._substitute_type_expr(te, mapping))

    def _compute_scoped_reindex(
        self,
        decl: ast.FnDecl,
        mapping: dict[str, str],
    ) -> dict[int, int]:
        """Scope-aware De Bruijn reindex for monomorphization (#769 gap 3).

        Returns ``{id(slot_ref_node): new_index}`` for every ``SlotRef`` in
        ``decl`` whose index changes when type-variable substitution merges
        formerly-distinct slot namespaces (``A -> Int, B -> Int``, or a
        type-var namespace merging with an already-concrete one — a body
        ``let @Int`` interposes for ``@A.0`` just the same).

        The pre-#769 implementation built a static ``(name, index) -> index``
        map from the PARAMETERS only and applied it body-wide.  That is
        unsound twice over: a ``let`` / match-binder / closure-param of a
        collapsing type interposes an extra binding for every LATER reference
        (one static entry cannot be right both before and after it), and the
        one-level slot-name truncation (``Array<Option<A>>`` ->
        ``"Array<Option>"``) hid genuine collapses entirely.

        This walker instead carries a binding stack of
        ``(old_name, new_name)`` pairs, pushed exactly where the checker
        binds slots — and therefore where the verifier's ``SlotEnv`` and
        codegen's ``WasmSlotEnv`` rebuild them when they consume the clone:

        * function parameters (in declaration order);
        * ``let`` / ``let``-destructuring bindings — pushed AFTER their RHS
          is walked (the RHS sees the pre-binding scope);
        * match-arm pattern binders, scoped to their arm, in left-to-right
          depth-first pattern order;
        * closure (``AnonFn``) parameters, pushed on the SHARED stack —
          closure bodies see enclosing bindings (spec ch. 5);
        * handler-clause operation parameters then handler state (clause
          scope, including the ``with`` state-update expression), and the
          handler state alone for the handled body — mirroring
          ``checker/control.py``;
        * block scopes push/pop, so an arm/branch ``let`` never leaks.

        Contracts (``requires``/``ensures``) resolve against a PARAMS-ONLY
        stack — they are boundary conditions, checked by the checker before
        the body binds anything, and both consumers rebuild exactly that
        scope for them.  ``where``-helpers are independent param-rooted
        scopes (their bodies cannot reference outer slots in any compiling
        program).  Refinement predicates are isolated single-binder scopes:
        the walker never descends into ``TypeExpr`` fields, so their indices
        are untouched (an outer collapse cannot shift a one-binder scope).

        Names are FULL-DEPTH canonical slot names (``vera/slots.py``, the
        shared namer both consumers resolve against).  A reference that does
        not resolve against the walked scope keeps its index — the consumers
        surface dangling refs (hard E699 in codegen) exactly as they would
        have pre-substitution.
        """
        out: dict[int, int] = {}
        stack: list[tuple[str | None, str | None]] = []

        def push(te: ast.TypeExpr) -> None:
            stack.append((
                type_expr_slot_name(te),
                self._substituted_slot_name(te, mapping),
            ))

        def resolve(ref: ast.SlotRef) -> None:
            name = slot_ref_name(ref)
            if name is None:
                return
            seen = 0
            for pos in range(len(stack) - 1, -1, -1):
                if stack[pos][0] != name:
                    continue
                if seen == ref.index:
                    binder_new = stack[pos][1]
                    if binder_new is None:
                        return
                    new_idx = sum(
                        1 for later in stack[pos + 1:]
                        if later[1] == binder_new
                    )
                    if new_idx != ref.index:
                        out[id(ref)] = new_idx
                    return
                seen += 1

        def push_pattern(pat: ast.Pattern) -> None:
            if isinstance(pat, ast.BindingPattern):
                push(pat.type_expr)
            elif isinstance(pat, ast.ConstructorPattern):
                for sub in pat.sub_patterns:
                    push_pattern(sub)
            # Wildcard / nullary / literal patterns bind nothing.

        def walk_stmt(stmt: ast.Stmt) -> None:
            if isinstance(stmt, ast.LetStmt):
                walk(stmt.value)
                push(stmt.type_expr)
                return
            if isinstance(stmt, ast.LetDestruct):
                walk(stmt.value)
                for te in stmt.type_bindings:
                    push(te)
                return
            walk(stmt)

        def walk(v: object) -> None:
            if isinstance(v, ast.SlotRef):
                resolve(v)
                return  # type_args carry no slot references
            if isinstance(v, ast.TypeExpr):
                return  # refinement predicates: isolated scopes, untouched
            if isinstance(v, ast.Block):
                mark = len(stack)
                for stmt in v.statements:
                    walk_stmt(stmt)
                walk(v.expr)
                del stack[mark:]
                return
            if isinstance(v, ast.MatchExpr):
                walk(v.scrutinee)
                for arm in v.arms:
                    mark = len(stack)
                    push_pattern(arm.pattern)
                    walk(arm.body)
                    del stack[mark:]
                return
            if isinstance(v, ast.AnonFn):
                mark = len(stack)
                for param_te in v.params:
                    push(param_te)
                walk(v.body)
                del stack[mark:]
                return
            if isinstance(v, ast.HandleExpr):
                if v.state is not None:
                    walk(v.state.init_expr)
                for clause in v.clauses:
                    mark = len(stack)
                    for param_te in clause.params:
                        push(param_te)
                    if v.state is not None:
                        push(v.state.type_expr)
                    walk(clause.body)
                    if clause.state_update is not None:
                        walk(clause.state_update[1])
                    del stack[mark:]
                # The HANDLED body carries NO state slot binding in the
                # consumers: codegen routes handler state through host-side
                # state cells (_translate_handle_state translates the body
                # with the env unchanged; _walk_free_vars likewise), so the
                # walker must not count one — a phantom binding shifts every
                # same-named ref in the body to a dangling or wrong local
                # (adversarial panel, PR #972).  The checker agrees since
                # #973: it binds no body-scope state either, rejecting such
                # refs with E130.  Clause scopes above keep params + state:
                # that is what _walk_free_vars counts (and Exn clause
                # compilation pushes the thrown binder).
                walk(v.body)
                return
            if isinstance(v, ast.Node):
                for fld in fields(v):
                    if fld.name == "span":
                        continue
                    walk(getattr(v, fld.name))
                return
            if isinstance(v, tuple):
                for item in v:
                    walk(item)

        def walk_fn_scope(fn_decl: ast.FnDecl) -> None:
            del stack[:]
            for param_te in fn_decl.params:
                push(param_te)
            for contract in fn_decl.contracts:
                walk(contract)
            walk(fn_decl.body)
            # ``where`` blocks nest — recurse so every helper at every depth
            # gets its own param-rooted scope, matching the total
            # collect_calls_in_node walk (PR #972 review; a depth-1 walk left
            # nested helpers' collapsed indices stale).
            for nested in fn_decl.where_fns or ():
                walk_fn_scope(nested)

        walk_fn_scope(decl)
        return out

    def _substitute_in_ast(
        self, node: ast.Node, mapping: dict[str, str],
        reindex: dict[int, int] | None = None,
    ) -> ast.Node:
        """Recursively substitute type variable names in an AST subtree.

        Handles NamedType (type expressions) and SlotRef (slot references)
        as special cases; all other nodes are walked generically via
        dataclass fields.

        When reindex is provided, De Bruijn indices on SlotRef nodes are
        adjusted to account for namespace collisions (e.g. A→Int, B→Int
        causing Array<A> and Array<B> to merge into Array<Int>).
        """
        # Special case: NamedType — substitute type variable names
        if isinstance(node, ast.NamedType):
            mapped = mapping.get(node.name)
            if mapped is not None and "<" in mapped:
                # Parameterized type like "Map<String, Int>" — parse into
                # NamedType with type_args
                return self._parse_type_name(mapped)
            new_name = mapped if mapped is not None else node.name
            new_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if new_name != node.name or new_args is not node.type_args:
                return replace(node, name=new_name, type_args=new_args)
            return node

        # Special case: SlotRef — substitute type_name and type_args,
        # and adjust the De Bruijn index if namespace collapse occurred
        # (scope-aware, keyed by node identity — see
        # ``_compute_scoped_reindex``).
        if isinstance(node, ast.SlotRef):
            mapped_name = mapping.get(node.type_name)
            if mapped_name is not None and "<" in mapped_name:
                # Parameterized type — parse into base name + type_args
                parsed = self._parse_type_name(mapped_name)
                new_type_name = parsed.name
                new_slot_args = parsed.type_args
            else:
                new_type_name = mapped_name if mapped_name is not None else node.type_name
                new_slot_args = node.type_args
            if node.type_args and new_slot_args is node.type_args:
                new_slot_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )

            # Adjust De Bruijn index if needed
            new_index = node.index
            if reindex:
                new_index = reindex.get(id(node), node.index)

            if (new_type_name != node.type_name
                    or new_slot_args is not node.type_args
                    or new_index != node.index):
                return replace(
                    node, type_name=new_type_name,
                    type_args=new_slot_args,
                    index=new_index,
                )
            return node

        # Special case: ResultRef — substitute type_name and type_args.  Parse a
        # parameterised mapping (T -> "Array<Int>") into base name + type_args,
        # mirroring the SlotRef/NamedType branches, so a generic postcondition's
        # @T.result becomes a canonical @Array<Int>.result rather than a
        # non-canonical type_name="Array<Int>" with no type_args (PR #767 review).
        if isinstance(node, ast.ResultRef):
            mapped_name = mapping.get(node.type_name)
            new_res_args: tuple[ast.TypeExpr, ...] | None
            if mapped_name is not None and "<" in mapped_name:
                parsed = self._parse_type_name(mapped_name)
                new_type_name = parsed.name
                new_res_args = parsed.type_args
            else:
                new_type_name = (
                    mapped_name if mapped_name is not None else node.type_name
                )
                new_res_args = node.type_args
            if node.type_args and new_res_args is node.type_args:
                new_res_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if (new_type_name != node.type_name
                    or new_res_args is not node.type_args):
                return replace(
                    node, type_name=new_type_name, type_args=new_res_args,
                )
            return node

        # Generic case: recurse into all dataclass fields
        changes: dict[str, Any] = {}
        for f in fields(node):
            if f.name == "span":
                continue
            val = getattr(node, f.name)
            new_val = self._substitute_value(val, mapping, reindex)
            if new_val is not val:
                changes[f.name] = new_val

        if changes:
            return replace(node, **changes)
        return node

    def _substitute_value(
        self, val: Any, mapping: dict[str, str],
        reindex: dict[int, int] | None = None,
    ) -> Any:
        """Recursively substitute type variables in a field value."""
        if isinstance(val, ast.Node):
            return self._substitute_in_ast(val, mapping, reindex)
        if isinstance(val, tuple):
            new_items = tuple(
                self._substitute_value(v, mapping, reindex) for v in val
            )
            if any(n is not o for n, o in zip(new_items, val)):
                return new_items
            return val
        return val

    def _substitute_type_expr(
        self, te: ast.TypeExpr, mapping: dict[str, str],
    ) -> ast.TypeExpr:
        """Substitute type variables in a TypeExpr, returning a TypeExpr."""
        result = self._substitute_in_ast(te, mapping)
        assert isinstance(result, ast.TypeExpr)  # noqa: S101
        return result
